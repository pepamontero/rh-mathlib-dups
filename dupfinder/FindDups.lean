/-
FindDups: list theorems of the RH project whose statement is literally a Mathlib theorem.

Usage (from inside a checkout of leanprover-community/riemann-hypothesis, with oleans fetched):

    lake env lean --run path/to/FindDups.lean <modules.txt> <out.csv>

`modules.txt` has one module name per line (e.g. `Lemmata.Foo.Bar`). The script imports
Mathlib plus those modules, and for every theorem declared in one of those modules it looks
for a theorem from Mathlib (or its dependencies) with the same type, up to renaming of bound
variables and universe parameters. Matches are written to `out.csv`.

This is a pure syntactic check (Tier 1): defeq-but-not-syntactically-equal statements are
not found.
-/
import Lean
import Std.Data.HashMap
import Std.Data.HashSet

open Lean

/-- Module roots that count as "library" code: Mathlib and everything it depends on. -/
def libRoots : List Name :=
  [`Mathlib, `Batteries, `Init, `Lean, `Std, `Lake, `Aesop, `Qq, `ProofWidgets,
   `Plausible, `ImportGraph, `LeanSearchClient]

def isLibModule (m : Name) : Bool := libRoots.contains m.getRoot

def isThm : ConstantInfo → Bool
  | .thmInfo _ => true
  | _ => false

/-- The type of a constant with its universe parameters renamed to `u_0, u_1, ...`,
so that two statements differing only in universe names get the same fingerprint. -/
def normType (ci : ConstantInfo) : Expr :=
  let us := ci.levelParams.mapIdx fun i _ => Level.param (Name.mkSimple s!"u_{i}")
  ci.type.instantiateLevelParams ci.levelParams us

def oleanExists (m : Name) : IO Bool := do
  try
    let p ← findOLean m
    p.pathExists
  catch _ =>
    pure false

def run (listFile outFile : String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let wanted : Array Name :=
    ((← IO.FS.lines listFile).filter (· ≠ "")).map String.toName
  -- Only import modules whose .olean is actually present (the cache may not cover all).
  let mut present : Array Name := #[]
  let mut missing := 0
  for m in wanted do
    if ← oleanExists m then
      present := present.push m
    else
      missing := missing + 1
  if present.isEmpty then
    IO.println s!"SUMMARY list={listFile} modules={wanted.size} missing_oleans={missing} \
      theorems_scanned=0 hits=0"
    IO.FS.writeFile outFile "rh_name,rh_module,mathlib_name,mathlib_module\n"
    return 0
  let shard : Std.HashSet Name := present.foldl (·.insert ·) {}
  let imports : Array Import := (#[`Mathlib] ++ present).map fun m => { module := m }
  let env ← importModules imports {} (trustLevel := 1024)
  let names := env.header.moduleNames
  let datas := env.header.moduleData
  -- 1. Fingerprint every library theorem.
  let mut tbl : Std.HashMap UInt64 (Array (Name × Name)) := {}
  let mut libThms := 0
  for i in [0:names.size] do
    let mod := names[i]!
    if isLibModule mod then
      for ci in datas[i]!.constants do
        if isThm ci && !ci.name.isInternal then
          libThms := libThms + 1
          let h := (normType ci).hash
          tbl := tbl.insert h ((tbl.getD h #[]).push (ci.name, mod))
  -- 2. Look up every theorem declared in this shard's modules.
  let out ← IO.FS.Handle.mk outFile .write
  out.putStrLn "rh_name,rh_module,mathlib_name,mathlib_module"
  let mut scanned := 0
  let mut hits := 0
  for i in [0:names.size] do
    let mod := names[i]!
    if shard.contains mod then
      for ci in datas[i]!.constants do
        if isThm ci && !ci.name.isInternal then
          scanned := scanned + 1
          let t := normType ci
          for (m, mmod) in tbl.getD t.hash #[] do
            if let some mci := env.find? m then
              -- `==` on `Expr` is alpha-equivalence, which rules out hash collisions.
              if normType mci == t then
                hits := hits + 1
                out.putStrLn s!"{ci.name},{mod},{m},{mmod}"
  out.flush
  IO.println s!"SUMMARY list={listFile} modules={wanted.size} missing_oleans={missing} \
    library_theorems={libThms} theorems_scanned={scanned} hits={hits}"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [listFile, outFile] =>
    try
      run listFile outFile
    catch e =>
      IO.eprintln s!"FindDups failed on {listFile}: {e}"
      return 2
  | _ =>
    IO.eprintln "usage: lake env lean --run FindDups.lean <modules.txt> <out.csv>"
    return 1
