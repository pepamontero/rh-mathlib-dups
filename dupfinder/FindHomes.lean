/-
FindHomes: for every declaration of the RH project, find where in Mathlib it could live.

Usage (from inside a checkout of leanprover-community/riemann-hypothesis, with oleans fetched):

    lake env lean --run path/to/FindHomes.lean <modules.txt> <out.csv>

`modules.txt` has one module name per line. The script imports Mathlib plus those modules and,
for every user-facing declaration of those modules, collects the constants its statement and
proof use. Auxiliary constants (`_proof_i`, `match_i`, ...) are looked through; constructors,
recursors, projections and equation lemmas count as their parent declaration.

* `layer` is 0 when everything the declaration uses comes from Mathlib (or its dependencies),
  and otherwise 1 + the largest layer among the project declarations it uses. Layer 0 is what
  could move to a `ToMathlib` folder today; layer k can move once layers below k have.
* For layer 0, `mathlib_homes` are the lowest Mathlib modules that (transitively) import every
  module the declaration uses, as `#find_home` computes them. The first one listed (the one with
  the fewest transitive imports) gives `proposed_file`, mirroring Mathlib's layout:
  `Mathlib.Data.ZMod.Basic` becomes `ToMathlib/Data/ZMod/Basic.lean`.

`status` is one of
* `ok`: one home;
* `ties`: several incomparable homes, the first was picked;
* `init_only`: uses nothing beyond `Init`, proposed `ToMathlib/Init.lean`;
* `no_common_home`: no Mathlib module imports everything it uses (only the `Mathlib` umbrella);
* `blocked`: layer > 0; `blocked_by` lists (up to 5 of) the project declarations it uses,
  highest layer first.

Like `#find_home`, this only sees constants: tactics, notation and options a proof relies on are
invisible, so a proposed move still has to be compiled to be confirmed.
-/
import Lean
import Std.Data.HashMap
import Std.Data.HashSet

open Lean

/-- Module roots that count as "library" code: Mathlib and everything it depends on.
Keep in sync with `FindDups.lean`. -/
def libRoots : List Name :=
  [`Mathlib, `Batteries, `Init, `Lean, `Std, `Lake, `Aesop, `Qq, `ProofWidgets,
   `Plausible, `ImportGraph, `LeanSearchClient]

def isLibModule (m : Name) : Bool := libRoots.contains m.getRoot

def oleanExists (m : Name) : IO Bool := do
  try
    let p ← findOLean m
    p.pathExists
  catch _ =>
    pure false

/-- The name without its `_private.<Module>.0.` prefix, if any. -/
def baseName (n : Name) : Name := (privateToUserName? n).getD n

def isNumeral (cs : List Char) : Bool := !cs.isEmpty && cs.all Char.isDigit

/-- How a project constant counts when another declaration uses it. -/
inductive Role where
  /-- A real declaration: a dependency in its own right. -/
  | user
  /-- An auxiliary constant (`_proof_i`, `match_i`, ...): use what it uses instead. -/
  | through
  /-- Generated together with another declaration (a constructor, recursor, projection,
  equation lemma ...): counts as that declaration. -/
  | owner (n : Name)
  deriving Inhabited

partial def role (env : Environment) (n : Name) : Role :=
  let b := baseName n
  if b.isInternal || Meta.isMatcherCore env n then .through
  else
    let up (p : Name) : Role := match role env p with
      | .owner o => .owner o
      | _ => .owner p
    match env.find? n with
    | some (.ctorInfo v) => .owner v.induct
    | some (.recInfo _) => up n.getPrefix
    | _ =>
      if isAuxRecursor env n || isNoConfusion env n || env.isProjectionFn n then up n.getPrefix
      else match b, env.find? n.getPrefix with
        -- Equation lemmas of a definition, injectivity / `sizeOf` lemmas of a constructor.
        | .str _ s, some (.defnInfo _) =>
          if s == "eq_def" || s == "eq_unfold" ||
              (s.startsWith "eq_" && isNumeral (s.toList.drop 3)) then
            up n.getPrefix
          else .user
        | .str _ s, some (.ctorInfo _) =>
          if s == "inj" || s == "injEq" || s == "sizeOf_spec" then up n.getPrefix else .user
        | _, _ => .user

/-- What a declaration uses, after looking through auxiliary constants: the project
declarations (by `Role`), and the indices of the non-`Init` library modules. -/
def usesOf (env : Environment) (isLib : Array Bool) (names : Array Name) (c : Name) :
    Array Name × Array Nat := Id.run do
  let mut proj : Std.HashSet Name := {}
  let mut libs : Std.HashSet Nat := {}
  let mut todo : Array Name := #[c]
  let mut seen : Std.HashSet Name := {c}
  while todo.size > 0 do
    let x := todo.back!
    todo := todo.pop
    let some ci := env.find? x | continue
    let mut used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
    -- An inductive's own type says little: its constructors' types carry the dependencies.
    if let .inductInfo v := ci then used := used ++ v.ctors.toArray
    for d in used do
      if seen.contains d then continue
      seen := seen.insert d
      let some mi := env.getModuleIdxFor? d | continue
      let mi := mi.toNat
      if isLib[mi]! then
        if names[mi]!.getRoot != `Init then libs := libs.insert mi
      else
        match role env d with
        | .through => todo := todo.push d
        | .owner o => if o != c then proj := proj.insert o
                      -- `c`'s own constructors: look at what they use.
                      else todo := todo.push d
        | .user => if d != c then proj := proj.insert d
  return (proj.toArray, libs.toArray)

structure St where
  layer : Std.HashMap Name Nat := {}
  proj : Std.HashMap Name (Array Name) := {}

/-- Compute the layer of `c` and of every project declaration below it, without recursion
(dependency chains can be very deep). Cycles (mutual definitions) are cut. -/
def ensureLayer (env : Environment) (isLib : Array Bool) (names : Array Name)
    (st0 : St) (c : Name) : St := Id.run do
  let mut st := st0
  if st.layer.contains c then return st
  let mut stack : Array Name := #[c]
  let mut onStack : Std.HashSet Name := {c}
  while stack.size > 0 do
    let top := stack.back!
    if st.layer.contains top then
      stack := stack.pop
      onStack := onStack.erase top
      continue
    let mut ds := #[]
    if let some cached := st.proj[top]? then
      ds := cached
    else
      ds := (usesOf env isLib names top).1
      st := { st with proj := st.proj.insert top ds }
    let pending := ds.filter fun d => !st.layer.contains d && !onStack.contains d
    if pending.isEmpty then
      let l := ds.foldl (init := 0) fun acc d => max acc ((st.layer[d]?.getD 0) + 1)
      st := { st with layer := st.layer.insert top l }
      stack := stack.pop
      onStack := onStack.erase top
    else
      for d in pending do
        stack := stack.push d
        onStack := onStack.insert d
  return st

/-- Number of set bits. -/
def popcount (n : Nat) : Nat := Id.run do
  let mut n := n
  let mut k := 0
  while n != 0 do
    n := n &&& (n - 1)
    k := k + 1
  return k

def kindOf (env : Environment) (n : Name) (ci : ConstantInfo) : String :=
  let k := if Meta.isInstanceCore env n then "instance" else match ci with
    | .thmInfo _ => "theorem"
    | .defnInfo _ => "def"
    | .inductInfo _ => if isStructure env n then "structure" else "inductive"
    | .axiomInfo _ => "axiom"
    | .opaqueInfo _ => "opaque"
    | _ => "other"
  if isPrivateName n then "private " ++ k else k

def csvField (s : String) : String :=
  if s.any (fun c => c == ',' || c == '"' || c == '\n') then
    "\"" ++ s.replace "\"" "\"\"" ++ "\""
  else s

def proposedFile (home : Name) : String :=
  let parts := home.components.map toString
  let parts := if home.getRoot == `Mathlib then parts.drop 1 else parts
  "ToMathlib/" ++ "/".intercalate parts ++ ".lean"

def header : String :=
  "rh_name,rh_module,kind,layer,status,proposed_file,mathlib_homes,blocked_by"

def run (listFile outFile : String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let wanted : Array Name :=
    ((← IO.FS.lines listFile).filter (· ≠ "")).map String.toName
  let mut present : Array Name := #[]
  let mut missing := 0
  for m in wanted do
    if ← oleanExists m then
      present := present.push m
    else
      missing := missing + 1
  if present.isEmpty then
    IO.println s!"SUMMARY list={listFile} modules={wanted.size} missing_oleans={missing} decls=0"
    IO.FS.writeFile outFile (header ++ "\n")
    return 0
  let shard : Std.HashSet Name := present.foldl (·.insert ·) {}
  let imports : Array Import := (#[`Mathlib] ++ present).map fun m => { module := m }
  let env ← importModules imports {} (trustLevel := 1024)
  let names := env.header.moduleNames
  let datas := env.header.moduleData
  let isLib := names.map isLibModule
  let idxOf : Std.HashMap Name Nat :=
    (names.zipIdx).foldl (fun m (n, i) => m.insert n i) {}
  -- Transitive imports of each library module, as a bitset over module indices.
  -- `moduleNames` lists every module after its imports.
  let mut closure : Array Nat := Array.replicate names.size 0
  for i in [0:names.size] do
    if isLib[i]! then
      let mut c := 1 <<< i
      for imp in datas[i]!.imports do
        if let some j := idxOf[imp.module]? then
          if isLib[j]! then c := c ||| closure[j]!
      closure := closure.set! i c
  let umbrella := idxOf[`Mathlib]?
  let mut homeMemo : Std.HashMap Nat (Array Nat) := {}
  let mut sizeMemo : Std.HashMap Nat Nat := {}
  let mut st : St := {}
  let out ← IO.FS.Handle.mk outFile .write
  out.putStrLn header
  let mut decls := 0
  let mut layerCounts : Std.HashMap Nat Nat := {}
  let mut statusCounts : Std.HashMap String Nat := {}
  let mut files : Std.HashSet String := {}
  for i in [0:names.size] do
    let mod := names[i]!
    unless shard.contains mod do continue
    for ci in datas[i]!.constants do
      let n := ci.name
      unless (role env n) matches .user do continue
      decls := decls + 1
      st := ensureLayer env isLib names st n
      let layer := st.layer[n]?.getD 0
      let (proj, libs) := usesOf env isLib names n
      let mut status := ""
      let mut homes : Array Nat := #[]
      let mut blocked : Array Name := #[]
      if layer > 0 then
        status := "blocked"
        blocked := (proj.qsort fun a b =>
          (st.layer[a]?.getD 0) > (st.layer[b]?.getD 0)).extract 0 5
      else
        -- Keep only the required modules that no other required module imports.
        let top := libs.filter fun r => !libs.any fun r' => r' != r && closure[r']!.testBit r
        if top.isEmpty then
          status := "init_only"
        else if top.size == 1 then
          homes := top
        else
          let mask := top.foldl (fun m r => m ||| (1 <<< r)) 0
          if let some hs := homeMemo[mask]? then
            homes := hs
          else
            let start := top.foldl max 0 + 1
            let mut cands : Array Nat := #[]
            for j in [start:names.size] do
              if isLib[j]! && some j != umbrella && closure[j]! &&& mask == mask then
                cands := cands.push j
            let cmask := cands.foldl (fun m j => m ||| (1 <<< j)) 0
            let mut hs := cands.filter fun j => closure[j]! &&& cmask == 1 <<< j
            -- Fewest transitive imports first.
            for j in hs do
              unless sizeMemo.contains j do sizeMemo := sizeMemo.insert j (popcount closure[j]!)
            hs := hs.qsort fun a b =>
              let sa := sizeMemo[a]?.getD 0
              let sb := sizeMemo[b]?.getD 0
              sa < sb || (sa == sb && names[a]!.toString < names[b]!.toString)
            homeMemo := homeMemo.insert mask hs
            homes := hs
        if status.isEmpty then
          status := if homes.isEmpty then "no_common_home"
            else if homes.size == 1 then "ok" else "ties"
      let file :=
        if status == "init_only" then "ToMathlib/Init.lean"
        else match homes[0]? with
          | some h => proposedFile names[h]!
          | none => ""
      unless file.isEmpty do files := files.insert file
      layerCounts := layerCounts.insert layer ((layerCounts[layer]?.getD 0) + 1)
      statusCounts := statusCounts.insert status ((statusCounts[status]?.getD 0) + 1)
      let homesStr := ";".intercalate (homes.toList.map fun h => names[h]!.toString)
      let blockedStr := ";".intercalate (blocked.toList.map fun b => (baseName b).toString)
      out.putStrLn <| ",".intercalate
        [csvField (baseName n).toString, mod.toString, kindOf env n ci, toString layer, status,
         file, csvField homesStr, csvField blockedStr]
  out.flush
  let layers := (layerCounts.toArray.qsort (·.1 < ·.1)).toList.map fun (l, k) => s!"{l}:{k}"
  let statuses := (statusCounts.toArray.qsort (·.1 < ·.1)).toList.map fun (s, k) => s!"{s}:{k}"
  IO.println s!"SUMMARY list={listFile} modules={wanted.size} missing_oleans={missing} \
    decls={decls} layers={",".intercalate layers} status={",".intercalate statuses} \
    proposed_files={files.size}"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [listFile, outFile] =>
    try
      run listFile outFile
    catch e =>
      IO.eprintln s!"FindHomes failed on {listFile}: {e}"
      return 2
  | _ =>
    IO.eprintln "usage: lake env lean --run FindHomes.lean <modules.txt> <out.csv>"
    return 1
