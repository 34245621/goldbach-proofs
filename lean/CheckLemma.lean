/-
The verifier half of the checker. Run by tools/check-lean.mjs, after the lemma file has been
built, as:

  lake exe checklemma <module> <statement file> <check|refute|reduce>

It never trusts what the lemma file printed or how it was elaborated. It reads the compiled
result and decides four things:

1. KERNEL. Every constant of every project module the lemma rests on is sent to the kernel
   again: the definitions root on top of the pinned modules it imports, everything else on top
   of the whole pinned library and the definitions root. A declaration that reached the
   compiled file without the kernel's agreement is refused here, and so is a project
   declaration that carries a name the pinned library or the definitions root already uses
   (but for a second copy of one of their theorems, same statement, which is left out: see
   `sameTheorem`).
2. THEOREM. The module declares a theorem whose name is the module's name.
3. AXIOMS. The theorem's transitive axioms, walked over the re-checked constants (not read from
   any cache the file could write), are inside the allowlist. `sorry` is the axiom `sorryAx`,
   so a `sorry` anywhere under the theorem is caught here, from the compiled proof.
4. STATEMENT. The recorded statement is elaborated in an environment made of the pinned
   library and the definitions root (`PEqualNP.Defs` and the modules under it) and nothing else
   of this project, whatever the lemma file imports. So nothing the lemma file or any helper
   module declares (an instance, a notation, a macro) can change what the text means, and a
   statement can only speak of the pinned library and the definitions root. The kernel then
   checks that the theorem is a proof of that statement (of its negation for `refute`), in an
   environment that extends the one the statement was read in.

For `reduce` (the decomposition door, ships dark) it also decides, in `reduceShape`: the theorem
is `T1 → ... → Tk → S`, 2 ≤ k ≤ 4 non-dependent arrows, the conclusion structurally the recorded
statement, each child a closed proposition of the statement environment, distinct, not `S`, not
`False`, and the module declares nothing but the theorem; each child is printed by Lean and read
back to the same term before its `CHILD` line is printed. Two screens on each child: TEXT (class
`reduce-child`: no string or name literal, no text type such as `String`, `Char`, `Lean.Name`
among its constants or their types, no constant of the meta namespaces `Lean`, `Std.Format`,
`IO` under it, no metadata node, at most 2000 printed characters) and WASTE (class
`reduce-waste`: the recorded statement is not a subterm of it, and `decide` of it, where an
instance exists, does not evaluate to `false` within a small budget).

On acceptance it also prints `MODULES` (every project module the theorem rests on) and `DEFS`
(the modules of the definitions root), which the wrapper turns into hashes for the artifact.

Exit 0: accepted. Exit 1: rejected, with one REJECTED line naming the class. Exit 3: the
verifier itself could not run.
-/
import Lean
open Lean

namespace PEqualNPChecker

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Roots of the libraries this project owns (lean/lakefile.toml). Everything else is a pinned dependency. -/
def projectRoots : List Name := [`PEqualNP, `Conjectures, `CheckerSuite]

def isProject (m : Name) : Bool := projectRoots.contains m.getRoot

/-- The definitions root: the one part of this project a recorded statement may speak of. -/
def defsRoot : Name := `PEqualNP.Defs

def isDefs (m : Name) : Bool := m == defsRoot || defsRoot.isPrefixOf m

/-- The pinned library a statement is read against, always the whole of it. -/
def statementLibrary : Name := `Mathlib

structure Walk where
  seen : NameSet := {}
  axioms : Array Name := #[]
  missing : Array Name := #[]

partial def walk (find : Name → Option ConstantInfo) (n : Name) : StateM Walk Unit := do
  if (← get).seen.contains n then return
  modify fun s => { s with seen := s.seen.insert n }
  match find n with
  | none => modify fun s => { s with missing := s.missing.push n }
  | some ci =>
    if ci matches .axiomInfo _ then modify fun s => { s with axioms := s.axioms.push n }
    for c in ci.getUsedConstantsAsSet do walk find c

def reject (cls msg : String) : IO UInt32 := do
  -- One line, always the last one printed: readers show the tail of the output.
  IO.println s!"REJECTED ({cls}): {msg.replace "\n" " "}"
  return 1

/-- No project module may declare a constant under this namespace: it is the checker's own. -/
def reserved : Name := `PEqualNPChecker

/-- A project constant `c` that carries the name of a constant `l` of the statement environment
is refused, with one exception, decided here: both are theorems, with the same universe
parameters and the same type. Lean writes some theorems on demand, in whichever module first
needs them (the equation lemmas `f.eq_1`, `f.eq_def`, ...): a project file that needs one and
does not import the pinned module that already holds it gets a second copy of its own, through
no act of its author.

Such a `c` is not accepted in place of `l`. It is LEFT OUT: it never reaches the kernel and never
enters the environment anything is checked in. Why nothing is lost:

* Every project constant that is kept is sent to the kernel on top of the statement environment,
  and there the name is `l`, the library's own theorem, with the library's own proof. Whatever
  `c`'s body says is never read by anything. So the final environment is the statement
  environment extended by kernel-accepted declarations only, as before; leaving a declaration
  out of the replay can only make the kernel refuse more (a kept constant that needed something
  `l` does not give), never accept more.
* A name still means one thing for the statement and for the proof: the name is `l` in both.
* The test is not what makes this sound (the point above holds for any left-out constant); it is
  what keeps the exception narrow. A term that names a theorem type-checks from its universe
  parameters and its type alone, and those are `l`'s exactly, so the honest file checks against
  `l` as it did against `c`. Everything else that collides is refused as before: a definition,
  an opaque, an axiom, an inductive type, a constructor, a recursor, a quotient constant on
  either side, a theorem whose type or universe parameters differ, a theorem against a
  non-theorem. `==` on `Expr` is equality up to bound variable names and binder annotations,
  neither of which the kernel reads; universe levels and constant names are compared exactly. -/
def sameTheorem (c l : ConstantInfo) : Bool :=
  match c, l with
  | .thmInfo c, .thmInfo l => c.levelParams == l.levelParams && c.type == l.type
  | _, _ => false

/-! ## The kind `reduce`: the runner side of the decomposition door.

A reduction file holds one theorem `M : T1 → ... → Tk → S`, 2 ≤ k ≤ 4, non-dependent arrows, `S`
the recorded statement. The `Ti` are the children: new steps the desk will post. `reduceShape`
decides everything the kind adds to `check`; the kernel check of `M` against `T1 → ... → Tk → S`
is the same one `check` runs. -/

def leadingForalls : Expr → Nat
  | .forallE _ _ b _ => leadingForalls b + 1
  | _ => 0

/-- The names of the bound variables inside a child are text of the file: they are replaced by
`x1, x2, ...` (by depth) before the child is printed. `==` does not read them. -/
partial def canonBinders (e : Expr) (d : Nat := 0) : Expr :=
  let x := Name.mkSimple s!"x{d + 1}"
  match e with
  | .forallE _ t b bi => .forallE x (canonBinders t d) (canonBinders b (d + 1)) bi
  | .lam _ t b bi => .lam x (canonBinders t d) (canonBinders b (d + 1)) bi
  | .letE _ t v b nd => .letE x (canonBinders t d) (canonBinders v d) (canonBinders b (d + 1)) nd
  | .app f a => .app (canonBinders f d) (canonBinders a d)
  | .mdata m b => .mdata m (canonBinders b d)
  | .proj s i b => .proj s i (canonBinders b d)
  | e => e

/-- How a child is printed: full names, the types of binders and numerals, proofs in full. -/
def childPpOptions : Options := Id.run do
  let mut o : Options := {}
  for n in [`pp.fullNames, `pp.funBinderTypes, `pp.numericTypes, `pp.proofs,
            `pp.structureInstanceTypes, `pp.letVarTypes] do
    o := o.setBool n true
  return o

def runMetaIn (env : Environment) (x : MetaM α) : IO α := do
  let ctx : Core.Context := { fileName := "<reduce>", fileMap := default, options := childPpOptions }
  let (a, _) ← (x.run' {} {}).toIO ctx { env }
  return a

/-- A constant of the judged module that Lean wrote for the theorem itself, not one its author
declared: a matcher of a `match` in the proof (and its splitter and equations), or a theorem
whose last name component is internal (an auxiliary lemma). -/
def generatedFor (env : Environment) (mod : Name) (c : ConstantInfo) : Bool :=
  mod.isPrefixOf c.name && c.name != mod &&
    (Meta.isMatcherCore env c.name ||
     (match c.name with
      | .str p _ => Meta.isMatcherCore env p || (Meta.isMatcherCore env p.getPrefix && !p.isAnonymous)
      | _ => false) ||
     (c matches .thmInfo _ && c.name.isInternal))

/-- The types that carry text. A child may not mention one (red team, pre-switch-on item A):
outside prose must never reach the desk dressed as a child statement. -/
def textTypes : List Name :=
  [`String, `Char, `Lean.Name, `Substring, `Substring.Raw, `String.Pos, `String.Pos.Raw,
   `String.Slice, `String.Iterator]

/-- The longest printed child, in characters. -/
def maxChildChars : Nat := 2000

/-- A constant of `t` that is a text type, or whose type mentions one (so `String.length`,
`Char.ofNat`, `Nat.toDigits` are caught without the type's name appearing in `t` itself). -/
def textConstant (env : Environment) (t : Expr) : Option (Name × Name) := Id.run do
  for c in t.getUsedConstants do
    if textTypes.contains c then return some (c, c)
    if let some ci := env.find? c then
      for d in ci.type.getUsedConstants do
        if textTypes.contains d then return some (c, d)
  return none

/-- The namespaces of Lean's own meta types (red team, last runner-side items): `Lean.Expr`,
`Lean.Syntax`, `Std.Format`, `IO` and their kin carry text and code, so a child may not rest on
them (`∀ e : Lean.Expr, e = e` would otherwise travel). -/
def metaRoots : List Name := [`Lean, `Std.Format, `Std.ToFormat, `IO, `EIO, `BaseIO]

def isMetaName (n : Name) : Bool := metaRoots.any (·.isPrefixOf n)

/-- `e` with the tactic script of every `autoParam α stx` dropped (only `α` kept). The script is
syntax Lean stores for the elaborator (`Lean.Syntax`, `Lean.Name`); the kernel reads `α`. -/
partial def dropAutoParamScripts (e : Expr) : Expr :=
  e.replace fun s =>
    if s.isAppOfArity ``autoParam 2 then some (dropAutoParamScripts s.appFn!.appArg!) else none

/-- A meta-namespace constant the child rests on, with the constant of the child the walk
started from. The walk is the dependency walk of `walk` with two cuts, both of things that
cannot carry a child's meaning: the values (proofs) of theorems, and the tactic scripts of
`autoParam`s in library declarations (the child's own term is read whole). Without the cuts,
`P ⊆ NP` reaches `Lean.Omega` through proofs and `Real.sqrt` reaches `Lean.Syntax` through
autoParam scripts. Constructors of inductive types are walked. -/
def metaConstant (env : Environment) (t : Expr) : Option (Name × Name) := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array (Name × Name) := t.getUsedConstants.reverse.map fun c => (c, c)
  while todo.size > 0 do
    let (c0, n) := todo[todo.size - 1]!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if isMetaName n then return some (c0, n)
    let some ci := env.find? n | continue
    let es := match ci with
      | .thmInfo _ => #[ci.type]
      | _ => #[ci.type] ++ ci.value?.toArray
    for e in es do
      for c in (dropAutoParamScripts e).getUsedConstants do
        unless seen.contains c do todo := todo.push (c0, c)
    if let .inductInfo v := ci then
      for c in v.ctors do todo := todo.push (c0, c)
  return none

/-- Does `decide t` evaluate to `false`? The evaluation is `whnf` at full transparency in
`MetaM`, under a small heartbeat budget; a `false` it finds is then confirmed by the kernel
(`Kernel.isDefEq (decide t) false`). No instance, a stuck term, an exhausted budget, an error,
or a kernel that does not agree: the answer is no. -/
def decidesFalse (env : Environment) (t : Expr) : IO Bool := do
  let r ← (runMetaIn env do
      let now ← IO.getNumHeartbeats
      withTheReader Core.Context (fun c => { c with maxHeartbeats := 20000 * 1000, initHeartbeats := now }) do
        let some inst ← Meta.synthInstance? (mkApp (mkConst ``Decidable) t) | return none
        let d := mkApp2 (mkConst ``Decidable.decide) t inst
        let v ← Meta.withTransparency .all (Meta.whnf d)
        return some (d, v)).toBaseIO
  let .ok (some (d, v)) := r | return false
  unless v == mkConst ``Bool.false do return false
  match Kernel.isDefEq env {} d (mkConst ``Bool.false) with
  | .ok b => return b
  | .error _ => return false

/-- Everything `reduce` adds to `check`. On success, the children with the text each is
printed as (which has been read back and checked by the kernel against the submitted child). -/
unsafe def reduceShape (stmtEnv : Environment) (modExtras : Option (Array Name)) (libEnv : Kernel.Environment)
    (checked : Name → Option ConstantInfo) (mod : Name) (thm : TheoremVal) (recorded : Expr) :
    IO (Except (String × String) (Array (Expr × String))) := do
  let fail (cls msg : String) : IO (Except (String × String) (Array (Expr × String))) :=
    pure (.error (cls, msg))
  -- SHAPE. The conclusion has as many leading binders as the recorded statement, so k is the
  -- number of leading binders of the theorem's type beyond those.
  let n := leadingForalls thm.type
  let m := leadingForalls recorded
  if n < m + 2 || n > m + 4 then
    return ← fail "reduce-shape" s!"{mod} must have the type T1 → ... → Tk → S with 2 ≤ k ≤ 4 children before the recorded statement S; it has {if n ≥ m then toString (n - m) else "fewer than 0"} leading binders beyond the {m} of S"
  let k := n - m
  let mut rest := thm.type
  let mut kids : Array Expr := #[]
  for i in [0:k] do
    let .forallE _ t b _ := rest | return ← fail "reduce-shape" "the theorem's type did not peel"
    if b.hasLooseBVar 0 then
      return ← fail "reduce-shape" s!"child {i + 1} of {mod} is a dependent binder: the rest of the type speaks of its proof. Each child must be a plain arrow T → ..."
    kids := kids.push t
    rest := b.lowerLooseBVars 1 1
  -- CONCLUSION: structurally equal to the recorded statement; defeq is not enough.
  unless rest == recorded do
    return ← fail "reduce-conclusion" s!"after its {k} children, {mod} concludes something that is not the recorded statement itself (structural equality; definitional equality is not enough)"
  -- CHILDREN
  for i in [0:k] do
    let t := kids[i]!
    let which := s!"child {i + 1} of {mod}"
    if t.hasLooseBVars then return ← fail "reduce-child" s!"{which} is not closed"
    if t.hasLevelParam || t.hasMVar || t.hasFVar then
      return ← fail "reduce-child" s!"{which} speaks of a universe parameter or a free variable; a child must be a closed proposition"
    let mut sw : Walk := {}
    for c in t.getUsedConstantsAsSet do
      sw := ((walk (fun n => if (libEnv.find? n).isSome then checked n else none) c).run sw).2
    unless sw.missing.isEmpty do
      return ← fail "reduce-child" s!"{which} rests on declarations outside the pinned library and the definitions root: {sw.missing.toList}. A child may only use what a recorded statement may use"
    let typed ← (runMetaIn stmtEnv do
        let ty ← Meta.whnf (← Meta.inferType t)
        return ty.isProp).toBaseIO
    let isProp ← match typed with
      | .ok b => pure b
      | .error e => return ← fail "reduce-child" s!"{which} could not be typed in the statement environment: {e}"
    unless isProp do return ← fail "reduce-child" s!"{which} is not a proposition"
    if t == mkConst ``False then return ← fail "reduce-child" s!"{which} is False"
    if t == recorded then return ← fail "reduce-child" s!"{which} is the recorded statement itself"
    for j in [0:i] do
      if t == kids[j]! then return ← fail "reduce-child" s!"children {j + 1} and {i + 1} of {mod} are the same proposition"
    -- TEXT cannot travel as a child: no string literal (string and name literals elaborate to
    -- terms with one; a character literal to `Char.ofNat`), no text type among its constants or
    -- their types.
    if (t.find? fun s => s matches .lit (.strVal _)).isSome then
      return ← fail "reduce-child" s!"{which} contains a string or name literal; text cannot travel as a child"
    if let some (c, d) := textConstant stmtEnv t then
      return ← fail "reduce-child" s!"{which} mentions {c}{if c == d then "" else s!", whose type speaks of {d}"}; a child may not speak of the text types {textTypes}"
    -- META: no constant of Lean's own meta types (Lean.*, Std.Format, IO, ...) under the child.
    if let some (c, d) := metaConstant stmtEnv t then
      return ← fail "reduce-child" s!"{which} rests on {d}{if c == d then "" else s!" (through {c})"}, of the meta namespaces {metaRoots}; meta types carry text and code, so a child may not use them"
    -- MDATA: Lean's metadata nodes (`no_index`, ...) carry key-value data, strings included, that
    -- printing drops; a child is a bare term.
    if (t.find? fun s => s matches .mdata ..).isSome then
      return ← fail "reduce-child" s!"{which} carries a metadata (mdata) node, for instance from `no_index`; metadata can carry text and is not printed, so a child is a bare term"
    -- WASTE: a child that holds the statement itself, or that is decidably false.
    if (t.find? (· == recorded)).isSome then
      return ← fail "reduce-waste" s!"{which} contains the recorded statement as a subterm; a child must be a new step, not the statement dressed up"
    if ← decidesFalse stmtEnv t then
      return ← fail "reduce-waste" s!"{which} is decidable and `decide` evaluates it to false (kernel-confirmed); a false child can never be closed"
  -- EXTRA: the module declares the theorem and nothing else.
  let some extra := modExtras
    | return ← fail "reduce-extra" s!"{mod} is not among the imported modules"
  unless extra.isEmpty do
    return ← fail "reduce-extra" s!"{mod} declares more than its theorem: {extra.toList}. A reduction file holds the one theorem and nothing else"
  -- PRINT, then read back: the text the desk posts must mean exactly the child.
  let mut out : Array (Expr × String) := #[]
  for i in [0:k] do
    let t := kids[i]!
    let which := s!"child {i + 1} of {mod}"
    let roundTrip (typedCoercions : Bool) : IO (Except String (Expr × String)) := do
      let printed ← (runMetaIn stmtEnv do
          let f ← withOptions (fun opts => opts.setBool `pp.coercions.types typedCoercions) <|
            Meta.ppExpr (canonBinders t)
          return (f.pretty 1000000).replace "\n" " ").toBaseIO
      let text ← match printed with
        | .ok s => pure s
        | .error e => return .error s!"could not be printed: {e}"
      if text.length > maxChildChars then
        return .error s!"prints as {text.length} characters; a child prints in at most {maxChildChars}"
      match Parser.runParserCategory stmtEnv `term text "<child>" with
      | .error e => return .error s!"prints as `{text}`, which is not one Lean term: {e}"
      | .ok _ => pure ()
      let src := "set_option autoImplicit false\ntheorem PEqualNPChecker.child :\n(\n" ++ text ++ "\n) := sorry\n"
      let (env', msgs) ← Elab.process src stmtEnv {} (fileName := "<child>")
      if msgs.hasErrors then
        return .error s!"prints as `{text}`, which does not elaborate again in the statement environment"
      let some back := env'.find? `PEqualNPChecker.child
        | return .error s!"prints as `{text}`, which did not elaborate to a declaration"
      unless back.levelParams.isEmpty do
        return .error s!"prints as `{text}`, which re-elaborates with universe parameters"
      if back.type == t then return .ok (back.type, text)
      unless typedCoercions do
        return .error s!"prints as `{text}`, which elaborates again to a different term"
      let .ok true := Kernel.isDefEq stmtEnv {} back.type t
        | return .error s!"prints as `{text}`, which is not definitionally equal to the submitted child"
      let mut sw : Walk := {}
      for c in back.type.getUsedConstantsAsSet do
        sw := ((walk (fun n => if (libEnv.find? n).isSome then checked n else none) c).run sw).2
      unless sw.missing.isEmpty && sw.axioms.all allowedAxioms.contains do
        return .error "re-elaborated type uses declarations or axioms outside the allowed statement environment"
      return .ok (back.type, text)
    -- Keep the original text when it round-trips. A coercion before an overloaded
    -- operation can require the target type to reconstruct the expression.
    let printedChild ← match ← roundTrip false with
      | .ok text => pure text
      | .error _ =>
        match ← roundTrip true with
        | .ok text => pure text
        | .error message => return ← fail "reduce-child" s!"{which} {message}"
    -- The final kernel witness uses the exact type read from the published text.
    out := out.push printedChild
  return .ok out

/-! ## Pointer-free kernel proof DAG (`KProof`) and persistent pre-warmed verifier.

A `.kproof` file carries ONLY the kernel declarations of one project module as a bottom-up
acyclic DAG (`Name`, `Level`, `Expr`, `ConstantInfo`). Every node at index `i` may reference only
indices `< i`, so the safe decoder (`decodeModule`, plain `def`, no `unsafe`) runs in flat `O(N)`
loops with zero recursion and zero C++ `.olean` pointer deserialization. -/

namespace KProof

def magic : ByteArray := "KPRF".toUTF8.push 1

def maxNames : Nat := 2000000
def maxLevels : Nat := 500000
def maxExprs : Nat := 50000000
def maxConstants : Nat := 200000
def maxListLen : Nat := 100000
def maxStrBytes : Nat := 4194304

partial def putVarNat (b : ByteArray) (n : Nat) : ByteArray :=
  if n < 128 then
    b.push n.toUInt8
  else
    putVarNat (b.push ((n % 128).toUInt8 ||| 0x80)) (n / 128)

def putByte (b : ByteArray) (x : UInt8) : ByteArray := b.push x

def putBool (b : ByteArray) (v : Bool) : ByteArray := b.push (if v then 1 else 0)

def putBytes (b : ByteArray) (bs : ByteArray) : ByteArray :=
  (putVarNat b bs.size) ++ bs

def putStr (b : ByteArray) (s : String) : ByteArray :=
  putBytes b s.toUTF8

def putNatList (b : ByteArray) (xs : List Nat) : ByteArray := Id.run do
  let mut out := putVarNat b xs.length
  for x in xs do
    out := putVarNat out x
  return out

partial def stripTopMData : Expr → Expr
  | .mdata _ e => stripTopMData e
  | e => e

structure ExportState where
  nameMap : Std.HashMap Name Nat := ({} : Std.HashMap Name Nat).insert .anonymous 0
  nameBuf : ByteArray := ByteArray.emptyWithCapacity 4096
  nameCount : Nat := 1
  levelMap : Std.HashMap Level Nat := ({} : Std.HashMap Level Nat).insert .zero 0
  levelBuf : ByteArray := ByteArray.emptyWithCapacity 512
  levelCount : Nat := 1
  exprPtrs : Std.HashMap USize (Expr × Nat) := {}
  exprBuf : ByteArray := ByteArray.emptyWithCapacity 65536
  exprCount : Nat := 0

partial def internName (n : Name) : StateM ExportState Nat := do
  if let some idx := (← get).nameMap[n]? then
    return idx
  match n with
  | .anonymous => return 0
  | .str p s =>
    let pidx ← internName p
    modifyGet fun st =>
      let idx := st.nameCount
      let buf := putStr (putVarNat (putByte st.nameBuf 1) pidx) s
      (idx, { st with nameMap := st.nameMap.insert n idx, nameBuf := buf, nameCount := idx + 1 })
  | .num p k =>
    let pidx ← internName p
    modifyGet fun st =>
      let idx := st.nameCount
      let buf := putVarNat (putVarNat (putByte st.nameBuf 2) pidx) k
      (idx, { st with nameMap := st.nameMap.insert n idx, nameBuf := buf, nameCount := idx + 1 })

partial def internLevel (u : Level) : StateM ExportState (Except String Nat) := do
  if let some idx := (← get).levelMap[u]? then
    return .ok idx
  match u with
  | .zero => return .ok 0
  | .succ v =>
    let .ok vidx ← internLevel v | return .error "level contains metavariable"
    modifyGet fun st =>
      let idx := st.levelCount
      let buf := putVarNat (putByte st.levelBuf 1) vidx
      (.ok idx, { st with levelMap := st.levelMap.insert u idx, levelBuf := buf, levelCount := idx + 1 })
  | .max v w =>
    let .ok vidx ← internLevel v | return .error "level contains metavariable"
    let .ok widx ← internLevel w | return .error "level contains metavariable"
    modifyGet fun st =>
      let idx := st.levelCount
      let buf := putVarNat (putVarNat (putByte st.levelBuf 2) vidx) widx
      (.ok idx, { st with levelMap := st.levelMap.insert u idx, levelBuf := buf, levelCount := idx + 1 })
  | .imax v w =>
    let .ok vidx ← internLevel v | return .error "level contains metavariable"
    let .ok widx ← internLevel w | return .error "level contains metavariable"
    modifyGet fun st =>
      let idx := st.levelCount
      let buf := putVarNat (putVarNat (putByte st.levelBuf 3) vidx) widx
      (.ok idx, { st with levelMap := st.levelMap.insert u idx, levelBuf := buf, levelCount := idx + 1 })
  | .param nm =>
    let nidx ← internName nm
    modifyGet fun st =>
      let idx := st.levelCount
      let buf := putVarNat (putByte st.levelBuf 4) nidx
      (.ok idx, { st with levelMap := st.levelMap.insert u idx, levelBuf := buf, levelCount := idx + 1 })
  | .mvar _ => return .error "level contains metavariable"

def encodeBinderInfo : BinderInfo → UInt8
  | .default => 0
  | .implicit => 1
  | .strictImplicit => 2
  | .instImplicit => 3

/-- Iterative post-order DAG interning: O(1) C stack depth regardless of expression depth. -/
unsafe def internExpr (root : Expr) : StateM ExportState (Except String Nat) := do
  let rootClean := stripTopMData root
  if let some (_, idx) := (← get).exprPtrs[ptrAddrUnsafe rootClean]? then
    return .ok idx
  let mut stack : Array (Expr × Bool) := #[(rootClean, false)]
  while stack.size > 0 do
    let (e, ready) := stack.back!
    stack := stack.pop
    let addr := ptrAddrUnsafe e
    if (← get).exprPtrs.contains addr then
      continue
    if !ready then
      stack := stack.push (e, true)
      match e with
      | .app f a =>
        stack := stack.push (stripTopMData a, false)
        stack := stack.push (stripTopMData f, false)
      | .lam _ t b _ | .forallE _ t b _ =>
        stack := stack.push (stripTopMData b, false)
        stack := stack.push (stripTopMData t, false)
      | .letE _ t v b _ =>
        stack := stack.push (stripTopMData b, false)
        stack := stack.push (stripTopMData v, false)
        stack := stack.push (stripTopMData t, false)
      | .proj _ _ s =>
        stack := stack.push (stripTopMData s, false)
      | .bvar _ | .sort _ | .const _ _ | .lit _ => pure ()
      | .fvar _ | .mvar _ | .mdata _ _ =>
        return .error "expression contains free or meta variables"
    else
      let lookupChild (child : Expr) : StateM ExportState Nat := do
        let c := stripTopMData child
        return ((← get).exprPtrs[ptrAddrUnsafe c]!).2
      let mut nodeBuf := (← get).exprBuf
      match e with
      | .bvar k =>
        nodeBuf := putVarNat (putByte nodeBuf 0) k
      | .sort u =>
        let .ok uidx ← internLevel u | return .error "sort level contains metavariable"
        nodeBuf := putVarNat (putByte nodeBuf 1) uidx
      | .const nm us =>
        let nidx ← internName nm
        let mut lidxs : List Nat := []
        for u in us do
          let .ok uidx ← internLevel u | return .error "const level contains metavariable"
          lidxs := uidx :: lidxs
        nodeBuf := putNatList (putVarNat (putByte nodeBuf 2) nidx) lidxs.reverse
      | .app f a =>
        let fidx ← lookupChild f
        let aidx ← lookupChild a
        nodeBuf := putVarNat (putVarNat (putByte nodeBuf 3) fidx) aidx
      | .lam nm t b bi =>
        let nidx ← internName nm
        let tidx ← lookupChild t
        let bidx ← lookupChild b
        nodeBuf := putByte (putVarNat (putVarNat (putVarNat (putByte nodeBuf 4) nidx) tidx) bidx) (encodeBinderInfo bi)
      | .forallE nm t b bi =>
        let nidx ← internName nm
        let tidx ← lookupChild t
        let bidx ← lookupChild b
        nodeBuf := putByte (putVarNat (putVarNat (putVarNat (putByte nodeBuf 5) nidx) tidx) bidx) (encodeBinderInfo bi)
      | .letE nm t v b nd =>
        let nidx ← internName nm
        let tidx ← lookupChild t
        let vidx ← lookupChild v
        let bidx ← lookupChild b
        nodeBuf := putBool (putVarNat (putVarNat (putVarNat (putVarNat (putByte nodeBuf 6) nidx) tidx) vidx) bidx) nd
      | .lit (.natVal k) =>
        nodeBuf := putVarNat (putByte nodeBuf 7) k
      | .lit (.strVal s) =>
        nodeBuf := putStr (putByte nodeBuf 8) s
      | .proj tn idx s =>
        let tnidx ← internName tn
        let sidx ← lookupChild s
        nodeBuf := putVarNat (putVarNat (putVarNat (putByte nodeBuf 9) tnidx) idx) sidx
      | .fvar _ | .mvar _ | .mdata _ _ =>
        return .error "unexpected open expression"
      modify fun st =>
        let idx := st.exprCount
        { st with exprPtrs := st.exprPtrs.insert addr (e, idx), exprBuf := nodeBuf, exprCount := idx + 1 }
  let some (_, finalIdx) := (← get).exprPtrs[ptrAddrUnsafe rootClean]?
    | return .error "internal DAG export miss"
  return .ok finalIdx

def internNameList (ns : List Name) : StateM ExportState (List Nat) :=
  ns.mapM internName

unsafe def encodeConstant (c : ConstantInfo) : StateM ExportState (Except String ByteArray) := do
  let nidx ← internName c.name
  let lps ← internNameList c.levelParams
  let .ok tidx ← internExpr c.type | return .error s!"failed to export type of {c.name}"
  let putHeader (tag : UInt8) : ByteArray :=
    putVarNat (putNatList (putVarNat (ByteArray.emptyWithCapacity 64 |>.push tag) nidx) lps) tidx
  match c with
  | .thmInfo v =>
    let .ok vidx ← internExpr v.value | return .error s!"failed to export proof of {c.name}"
    let all ← internNameList v.all
    return .ok (putNatList (putVarNat (putHeader 0) vidx) all)
  | .defnInfo v =>
    let .ok vidx ← internExpr v.value | return .error s!"failed to export value of {c.name}"
    let all ← internNameList v.all
    let (htag, hval) : UInt8 × Nat := match v.hints with
      | .opaque => (0, 0) | .abbrev => (1, 0) | .regular h => (2, h.toNat)
    let stag : UInt8 := match v.safety with
      | .unsafe => 0 | .safe => 1 | .partial => 2
    return .ok (putNatList (putByte (putVarNat (putByte (putVarNat (putHeader 1) vidx) htag) hval) stag) all)
  | .opaqueInfo v =>
    let .ok vidx ← internExpr v.value | return .error s!"failed to export opaque value of {c.name}"
    let all ← internNameList v.all
    return .ok (putNatList (putBool (putVarNat (putHeader 2) vidx) v.isUnsafe) all)
  | .axiomInfo v =>
    return .ok (putBool (putHeader 3) v.isUnsafe)
  | .inductInfo v =>
    let all ← internNameList v.all
    let ctors ← internNameList v.ctors
    let mut b := putHeader 4
    b := putVarNat (putVarNat b v.numParams) v.numIndices
    b := putNatList (putNatList b all) ctors
    b := putBool (putBool (putBool (putVarNat b v.numNested) v.isRec) v.isUnsafe) v.isReflexive
    return .ok b
  | .ctorInfo v =>
    let indIdx ← internName v.induct
    let mut b := putHeader 5
    b := putBool (putVarNat (putVarNat (putVarNat (putVarNat b indIdx) v.cidx) v.numParams) v.numFields) v.isUnsafe
    return .ok b
  | .recInfo v =>
    let all ← internNameList v.all
    let mut b := putNatList (putHeader 6) all
    b := putVarNat (putVarNat (putVarNat (putVarNat b v.numParams) v.numIndices) v.numMotives) v.numMinors
    b := putVarNat b v.rules.length
    for r in v.rules do
      let cidx ← internName r.ctor
      let .ok ridx ← internExpr r.rhs | return .error s!"failed to export recursor rhs of {c.name}"
      b := putVarNat (putVarNat (putVarNat b cidx) r.nfields) ridx
    b := putBool (putBool b v.k) v.isUnsafe
    return .ok b
  | .quotInfo _ =>
    return .error s!"quotient primitive {c.name} cannot be declared in a user module"

unsafe def encodeModule (mod : Name) (extras : Array Name) (constants : Array ConstantInfo) :
    Except String ByteArray := Id.run do
  let runExport : StateM ExportState (Except String (Nat × List Nat × ByteArray)) := do
    let midx ← internName mod
    let eidxs ← internNameList extras.toList
    let mut cbuf := putVarNat (ByteArray.emptyWithCapacity 4096) constants.size
    for c in constants do
      match ← encodeConstant c with
      | .error msg => return .error msg
      | .ok encoded => cbuf := cbuf ++ encoded
    return .ok (midx, eidxs, cbuf)
  let (res, st) := runExport.run {}
  match res with
  | .error msg => return .error msg
  | .ok (midx, eidxs, cbuf) =>
    let mut out := magic
    out := (putVarNat out st.nameCount) ++ st.nameBuf
    out := (putVarNat out st.levelCount) ++ st.levelBuf
    out := (putVarNat out st.exprCount) ++ st.exprBuf
    out := putNatList (putVarNat out midx) eidxs
    out := out ++ cbuf
    return .ok out

structure DecodedModule where
  module : Name
  extras : Array Name
  constants : Array ConstantInfo

abbrev DecodeM := StateT Nat (Except String)

def readByte (bs : ByteArray) : DecodeM UInt8 := do
  let pos ← get
  if h : pos < bs.size then
    set (pos + 1)
    return bs[pos]
  else
    throw "unexpected end of kproof stream"

def readBool (bs : ByteArray) : DecodeM Bool := do
  match ← readByte bs with
  | 0 => return false
  | 1 => return true
  | _ => throw "invalid boolean byte in kproof"

def readVarNatBounded (bs : ByteArray) (maxBytes : Nat) : DecodeM Nat := do
  let mut acc : Nat := 0
  let mut shift : Nat := 0
  for _ in [0:maxBytes] do
    let byte ← readByte bs
    acc := acc + ((byte &&& 0x7f).toNat <<< shift)
    if (byte &&& 0x80) == 0 then
      return acc
    shift := shift + 7
  throw "varint exceeds byte limit in kproof"

def readCount (bs : ByteArray) (limit : Nat) : DecodeM Nat := do
  let n ← readVarNatBounded bs 10
  if n > limit then
    throw s!"kproof count {n} exceeds limit {limit}"
  return n

def readBigNat (bs : ByteArray) : DecodeM Nat :=
  readVarNatBounded bs 65536

def readStr (bs : ByteArray) : DecodeM String := do
  let len ← readCount bs maxStrBytes
  let pos ← get
  if pos + len > bs.size then
    throw "truncated string in kproof"
  set (pos + len)
  match String.fromUTF8? (bs.extract pos (pos + len)) with
  | some s => return s
  | none => throw "invalid UTF-8 string in kproof"

def getAt (arr : Array α) (idx : Nat) (label : String) : DecodeM α := do
  if h : idx < arr.size then
    return arr[idx]
  else
    throw s!"out-of-bounds {label} index {idx} (size {arr.size})"

def readIndexedList (bs : ByteArray) (arr : Array α) (label : String) : DecodeM (List α) := do
  let len ← readCount bs maxListLen
  let mut out : Array α := Array.mkEmpty len
  for _ in [0:len] do
    let idx ← readVarNatBounded bs 10
    out := out.push (← getAt arr idx label)
  return out.toList

/-- Total, non-recursive, memory-safe decoder for `KProof` binary DAGs. -/
def decodeModule (bs : ByteArray) : Except String DecodedModule := do
  if bs.size < magic.size || bs.extract 0 magic.size != magic then
    throw "invalid kproof header magic"
  let action : DecodeM DecodedModule := do
    let nNames ← readCount bs maxNames
    if nNames < 1 then throw "kproof name table must include anonymous root"
    let mut names : Array Name := Array.mkEmpty nNames
    names := names.push .anonymous
    for _ in [1:nNames] do
      let tag ← readByte bs
      let pidx ← readVarNatBounded bs 10
      let parent ← getAt names pidx "name parent"
      match tag with
      | 1 => names := names.push (.str parent (← readStr bs))
      | 2 => names := names.push (.num parent (← readBigNat bs))
      | _ => throw s!"invalid name tag {tag}"

    let nLevels ← readCount bs maxLevels
    if nLevels < 1 then throw "kproof level table must include zero root"
    let mut levels : Array Level := Array.mkEmpty nLevels
    levels := levels.push .zero
    for _ in [1:nLevels] do
      let tag ← readByte bs
      match tag with
      | 1 =>
        let u ← getAt levels (← readVarNatBounded bs 10) "level"
        levels := levels.push (.succ u)
      | 2 =>
        let u ← getAt levels (← readVarNatBounded bs 10) "level"
        let v ← getAt levels (← readVarNatBounded bs 10) "level"
        levels := levels.push (.max u v)
      | 3 =>
        let u ← getAt levels (← readVarNatBounded bs 10) "level"
        let v ← getAt levels (← readVarNatBounded bs 10) "level"
        levels := levels.push (.imax u v)
      | 4 =>
        let nm ← getAt names (← readVarNatBounded bs 10) "level param name"
        levels := levels.push (.param nm)
      | _ => throw s!"invalid level tag {tag}"

    let decodeBI (b : UInt8) : DecodeM BinderInfo :=
      match b with
      | 0 => return .default
      | 1 => return .implicit
      | 2 => return .strictImplicit
      | 3 => return .instImplicit
      | _ => throw s!"invalid binder info {b}"

    let nExprs ← readCount bs maxExprs
    let mut exprs : Array Expr := Array.mkEmpty nExprs
    for _ in [0:nExprs] do
      let tag ← readByte bs
      match tag with
      | 0 => exprs := exprs.push (.bvar (← readVarNatBounded bs 10))
      | 1 => exprs := exprs.push (.sort (← getAt levels (← readVarNatBounded bs 10) "sort level"))
      | 2 =>
        let nm ← getAt names (← readVarNatBounded bs 10) "const name"
        let us ← readIndexedList bs levels "const level"
        exprs := exprs.push (.const nm us)
      | 3 =>
        let f ← getAt exprs (← readVarNatBounded bs 10) "app fn"
        let a ← getAt exprs (← readVarNatBounded bs 10) "app arg"
        exprs := exprs.push (.app f a)
      | 4 =>
        let nm ← getAt names (← readVarNatBounded bs 10) "lam binder"
        let ty ← getAt exprs (← readVarNatBounded bs 10) "lam type"
        let bd ← getAt exprs (← readVarNatBounded bs 10) "lam body"
        let bi ← decodeBI (← readByte bs)
        exprs := exprs.push (.lam nm ty bd bi)
      | 5 =>
        let nm ← getAt names (← readVarNatBounded bs 10) "forall binder"
        let ty ← getAt exprs (← readVarNatBounded bs 10) "forall type"
        let bd ← getAt exprs (← readVarNatBounded bs 10) "forall body"
        let bi ← decodeBI (← readByte bs)
        exprs := exprs.push (.forallE nm ty bd bi)
      | 6 =>
        let nm ← getAt names (← readVarNatBounded bs 10) "let binder"
        let ty ← getAt exprs (← readVarNatBounded bs 10) "let type"
        let vl ← getAt exprs (← readVarNatBounded bs 10) "let val"
        let bd ← getAt exprs (← readVarNatBounded bs 10) "let body"
        let nd ← readBool bs
        exprs := exprs.push (.letE nm ty vl bd nd)
      | 7 => exprs := exprs.push (.lit (.natVal (← readBigNat bs)))
      | 8 => exprs := exprs.push (.lit (.strVal (← readStr bs)))
      | 9 =>
        let tn ← getAt names (← readVarNatBounded bs 10) "proj type"
        let idx ← readVarNatBounded bs 10
        let st ← getAt exprs (← readVarNatBounded bs 10) "proj struct"
        exprs := exprs.push (.proj tn idx st)
      | _ => throw s!"invalid expr tag {tag}"

    let mod ← getAt names (← readVarNatBounded bs 10) "module name"
    let extrasList ← readIndexedList bs names "module extra"
    let nConsts ← readCount bs maxConstants
    let mut consts : Array ConstantInfo := Array.mkEmpty nConsts
    for _ in [0:nConsts] do
      let ctag ← readByte bs
      let cName ← getAt names (← readVarNatBounded bs 10) "decl name"
      let lps ← readIndexedList bs names "level param"
      let cType ← getAt exprs (← readVarNatBounded bs 10) "decl type"
      let base : ConstantVal := { name := cName, levelParams := lps, type := cType }
      match ctag with
      | 0 =>
        let val ← getAt exprs (← readVarNatBounded bs 10) "thm value"
        let all ← readIndexedList bs names "thm all"
        consts := consts.push (.thmInfo { toConstantVal := base, value := val, all })
      | 1 =>
        let val ← getAt exprs (← readVarNatBounded bs 10) "defn value"
        let htag ← readByte bs
        let hval ← readVarNatBounded bs 10
        let hints : ReducibilityHints ← match htag with
          | 0 => pure .opaque
          | 1 => pure .abbrev
          | 2 => pure (.regular hval.toUInt32)
          | _ => throw s!"invalid reducibility hint {htag}"
        let safety : DefinitionSafety ← match ← readByte bs with
          | 0 => pure .unsafe
          | 1 => pure .safe
          | 2 => pure .partial
          | s => throw s!"invalid definition safety {s}"
        let all ← readIndexedList bs names "defn all"
        consts := consts.push (.defnInfo { toConstantVal := base, value := val, hints, safety, all })
      | 2 =>
        let val ← getAt exprs (← readVarNatBounded bs 10) "opaque value"
        let isUnsafe ← readBool bs
        let all ← readIndexedList bs names "opaque all"
        consts := consts.push (.opaqueInfo { toConstantVal := base, value := val, isUnsafe, all })
      | 3 =>
        let isUnsafe ← readBool bs
        consts := consts.push (.axiomInfo { toConstantVal := base, isUnsafe })
      | 4 =>
        let numParams ← readVarNatBounded bs 10
        let numIndices ← readVarNatBounded bs 10
        let all ← readIndexedList bs names "induct all"
        let ctors ← readIndexedList bs names "induct ctors"
        let numNested ← readVarNatBounded bs 10
        let isRec ← readBool bs
        let isUnsafe ← readBool bs
        let isReflexive ← readBool bs
        consts := consts.push (.inductInfo {
          toConstantVal := base, numParams, numIndices, all, ctors, numNested, isRec, isUnsafe, isReflexive
        })
      | 5 =>
        let induct ← getAt names (← readVarNatBounded bs 10) "ctor induct"
        let cidx ← readVarNatBounded bs 10
        let numParams ← readVarNatBounded bs 10
        let numFields ← readVarNatBounded bs 10
        let isUnsafe ← readBool bs
        consts := consts.push (.ctorInfo { toConstantVal := base, induct, cidx, numParams, numFields, isUnsafe })
      | 6 =>
        let all ← readIndexedList bs names "rec all"
        let numParams ← readVarNatBounded bs 10
        let numIndices ← readVarNatBounded bs 10
        let numMotives ← readVarNatBounded bs 10
        let numMinors ← readVarNatBounded bs 10
        let nRules ← readCount bs maxListLen
        let mut rules : Array RecursorRule := Array.mkEmpty nRules
        for _ in [0:nRules] do
          let ctor ← getAt names (← readVarNatBounded bs 10) "rec rule ctor"
          let nfields ← readVarNatBounded bs 10
          let rhs ← getAt exprs (← readVarNatBounded bs 10) "rec rule rhs"
          rules := rules.push { ctor, nfields, rhs }
        let k ← readBool bs
        let isUnsafe ← readBool bs
        consts := consts.push (.recInfo {
          toConstantVal := base, all, numParams, numIndices, numMotives, numMinors, rules := rules.toList, k, isUnsafe
        })
      | _ => throw s!"invalid constant tag {ctag}"

    let endPos ← get
    if endPos != bs.size then
      throw s!"trailing bytes in kproof ({bs.size - endPos} extra bytes)"
    return { module := mod, extras := extrasList.toArray, constants := consts }
  (action.run magic.size).map Prod.fst

end KProof

structure StmtContext where
  stmtEnv : Environment
  stmtModules : Array Name
  libEnv : Kernel.Environment
  defsConsts : Std.HashMap Name ConstantInfo
  defsModules : Array Name

def formatReject (cls msg : String) : UInt32 × Array String :=
  (1, #[s!"REJECTED ({cls}): {msg.replace "\n" " "}"])

unsafe def loadStmtContext : IO (Except (UInt32 × Array String) StmtContext) := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let stmtEnv ← importModules #[{ module := statementLibrary }, { module := defsRoot }] {}
    (trustLevel := 0) (loadExts := true)
  let stmtModules := stmtEnv.header.moduleNames
  let mut defsConsts : Std.HashMap Name ConstantInfo := {}
  let mut defsBaseImports : Array Import := #[{ module := `Init }]
  let mut defsModules : Array Name := #[]
  for i in [0:stmtModules.size] do
    let m := stmtModules[i]!
    if isProject m then
      unless isDefs m do
        return .error (formatReject "defs-root" s!"the statement environment reached {m}, which is outside the definitions root")
      defsModules := defsModules.push m
      let d := stmtEnv.header.moduleData[i]!
      for c in d.constants do
        if reserved.isPrefixOf c.name then
          return .error (formatReject "reserved-name" s!"{m} declares {c.name}; names under {reserved} belong to the checker")
        defsConsts := defsConsts.insert c.name c
      for imp in d.imports do
        if isProject imp.module then
          unless isDefs imp.module do
            return .error (formatReject "defs-root" s!"{m}, in the definitions root, imports {imp.module}, which is outside it. The definitions root may import only the pinned library and itself")
        else unless defsBaseImports.any (·.module == imp.module) do
          defsBaseImports := defsBaseImports.push { module := imp.module }
  let defsBase ← importModules defsBaseImports {} (trustLevel := 0)
  try
    discard <| defsBase.toKernelEnv.replay defsConsts
  catch e =>
    return .error (formatReject "kernel" s!"the kernel refused a declaration of the definitions root: {e}")
  return .ok {
    stmtEnv, stmtModules, libEnv := stmtEnv.toKernelEnv, defsConsts, defsModules
  }

unsafe def verifyLoaded (ctx : StmtContext) (mod : Name) (stmt kind : String)
    (projectModules : Array Name) (defsModules : Array Name)
    (consts : Std.HashMap Name ConstantInfo) (modExtras : Option (Array Name)) :
    IO (UInt32 × Array String) := do
  let { stmtEnv, stmtModules, libEnv, defsConsts, .. } := ctx
  let mut out : Array String := #[]
  -- 1. KERNEL
  let kenv ← try
      pure (← libEnv.replay consts)
    catch e =>
      return formatReject "kernel" s!"the kernel refused a declaration under {mod}: {e}"
  let checked (n : Name) : Option ConstantInfo := do
    let ci ← kenv.find? n
    match stmtEnv.getModuleIdxFor? n with
    | some idx =>
      if isProject stmtModules[idx.toNat]! then
        let c ← defsConsts[n]?
        if c.isUnsafe || c.isPartial then none else some ci
      else some ci
    | none => if ci.isUnsafe || ci.isPartial then none else some ci

  -- 2. THEOREM
  let some ci := checked mod
    | return formatReject "no-theorem" s!"the file declares no theorem named {mod} (one lemma, one file: the theorem carries the module's name)"
  let .thmInfo thm := ci
    | return formatReject "no-theorem" s!"{mod} is not a theorem"

  -- 3. AXIOMS
  let (_, w) := (walk checked mod).run {}
  unless w.missing.isEmpty do
    return formatReject "kernel" s!"{mod} rests on constants the kernel never accepted: {w.missing.toList}"
  if w.axioms.contains ``sorryAx then
    return formatReject "sorry" s!"{mod} rests on sorry (read from the compiled proof)"
  let extra := w.axioms.filter (!allowedAxioms.contains ·)
  unless extra.isEmpty do
    return formatReject "axiom" s!"{mod} rests on axioms outside the allowlist: {extra.toList}"

  -- 4. STATEMENT
  match Parser.runParserCategory stmtEnv `term stmt "<recorded statement>" with
  | .error e => return formatReject "statement" s!"the recorded statement is not one Lean term: {e}"
  | .ok _ => pure ()
  let src := "set_option autoImplicit false\ntheorem PEqualNPChecker.recorded :\n(\n" ++ stmt ++ "\n) := sorry\n"
  let (stmtEnv', msgs) ← Elab.process src stmtEnv {} (fileName := "<recorded statement>")
  if msgs.hasErrors then
    for m in msgs.toList do
      if m.severity matches .error then out := out.push (← m.toString)
    let (_, rej) := formatReject "statement" s!"the recorded statement does not elaborate. A statement may only use the pinned library and the definitions root ({defsRoot}); nothing declared in a lemma file or a helper module exists for it"
    return (1, out ++ rej)
  let some rec := stmtEnv'.find? `PEqualNPChecker.recorded
    | return formatReject "statement" "the recorded statement did not produce a declaration"
  let mut sw : Walk := {}
  for c in rec.type.getUsedConstantsAsSet do
    sw := ((walk (fun n => if (libEnv.find? n).isSome then checked n else none) c).run sw).2
  unless sw.missing.isEmpty do
    return formatReject "statement" s!"the recorded statement rests on declarations that are not in the pinned library or the definitions root as the kernel accepted them: {sw.missing.toList}. Write it as one term that needs no auxiliary declaration"
  unless rec.levelParams.length == thm.levelParams.length do
    return formatReject "statement" s!"universe parameters differ: recorded {rec.levelParams}, proved {thm.levelParams}"
  let us := thm.levelParams.map mkLevelParam
  let recorded := rec.type.instantiateLevelParams rec.levelParams us
  let mut goal := if kind == "refute" then mkApp (mkConst ``Not) recorded else recorded
  let mut children : Array (Expr × String) := #[]
  if kind == "reduce" then
    match ← reduceShape stmtEnv modExtras libEnv checked mod thm recorded with
    | .error (cls, msg) => return formatReject cls msg
    | .ok cs =>
      children := cs
      goal := cs.foldr (fun (t, _) b => mkForall `h .default t b) recorded
  let witness := Declaration.thmDecl {
    name := `PEqualNPChecker.witness, levelParams := thm.levelParams, type := goal, value := mkConst mod us }
  match kenv.addDeclCore 0 0 witness (cancelTk? := none) with
  | .ok _ => pure ()
  | .error ex =>
    let what := if kind == "refute" then "the negation of the recorded statement" else "the recorded statement"
    let why ← try (ex.toMessageData {}).toString catch _ => pure "(the kernel's message could not be printed)"
    out := out.push s!"kernel: {why}"
    let (_, rej) := formatReject "statement" s!"{mod} is not a proof of {what}. It proves: {thm.type}"
    return (1, out ++ rej)

  if kind == "reduce" then out := out.push s!"CHILDREN {children.size}"
  for h : i in [0:children.size] do
    out := out.push s!"CHILD {i + 1} {children[i].2}"
  out := out.push s!"MODULES {" ".intercalate (projectModules.filter (!isDefs ·) |>.toList.map toString)}"
  out := out.push s!"DEFS {" ".intercalate (defsModules.toList.map toString)}"
  out := out.push s!"ACCEPTED ({kind}): {mod}; axioms {w.axioms.toList}; kernel re-checked {consts.size + defsConsts.size} constants of {(defsModules ++ projectModules.filter (!isDefs ·)).toList}"
  return (0, out)

def emitResult (res : UInt32 × Array String) : IO UInt32 := do
  for line in res.2 do
    IO.println line
  return res.1

unsafe def run (modStr stmtPath kind : String) : IO UInt32 := do
  let mod := modStr.toName
  unless kind == "check" || kind == "refute" || kind == "reduce" do
    IO.eprintln s!"kind must be check, refute or reduce, got {kind}"; return 3
  let stmt ← IO.FS.readFile stmtPath
  let ctx ← match ← loadStmtContext with
    | .error res => return ← emitResult res
    | .ok c => pure c

  let full ← importModules #[{ module := mod }] {} (trustLevel := 0)
  let names := full.header.moduleNames
  let mut consts : Std.HashMap Name ConstantInfo := {}
  let mut projectModules : Array Name := #[]
  let mut defsModules := ctx.defsModules
  for i in [0:names.size] do
    let m := names[i]!
    if isProject m && !ctx.stmtModules.contains m then
      let d := full.header.moduleData[i]!
      projectModules := projectModules.push m
      if isDefs m then
        defsModules := defsModules.push m
        for imp in d.imports do
          if isProject imp.module && !isDefs imp.module then
            return ← emitResult (formatReject "defs-root" s!"{m}, in the definitions root, imports {imp.module}, which is outside it. The definitions root may import only the pinned library and itself")
      for c in d.constants do
        if reserved.isPrefixOf c.name then
          return ← emitResult (formatReject "reserved-name" s!"{m} declares {c.name}; names under {reserved} belong to the checker")
        if let some l := ctx.libEnv.find? c.name then
          if sameTheorem c l then continue
          return ← emitResult (formatReject "redeclares" s!"{m} declares {c.name}, a name the pinned library or the definitions root already declares. A project module may not declare it again")
        consts := consts.insert c.name c
  unless names.contains mod && isProject mod do
    return ← emitResult (formatReject "not-a-project-module" s!"{mod} is not under one of the project's libraries")

  let modExtras : Option (Array Name) := full.header.moduleNames.idxOf? mod |>.map fun idx => Id.run do
    let mut extra : Array Name := #[]
    for c in full.header.moduleData[idx]!.constants do
      unless c.name == mod || generatedFor full mod c do extra := extra.push c.name
    return extra
  emitResult (← verifyLoaded ctx mod stmt kind projectModules defsModules consts modExtras)

unsafe def exportKProofFile (modStr outPath : String) : IO UInt32 := do
  let mod := modStr.toName
  unless isProject mod && !isDefs mod do
    IO.eprintln s!"cannot export non-proof module {mod}"; return 1
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let full ← importModules #[{ module := mod }] {} (trustLevel := 0)
  let some idx := full.header.moduleNames.idxOf? mod
    | IO.eprintln s!"module {mod} not found in imported header"; return 1
  let d := full.header.moduleData[idx]!
  let mut extras : Array Name := #[]
  for c in d.constants do
    unless c.name == mod || generatedFor full mod c do extras := extras.push c.name
  match KProof.encodeModule mod extras d.constants with
  | .error msg => IO.eprintln s!"kproof export failed: {msg}"; return 1
  | .ok bytes =>
    IO.FS.writeBinFile outPath bytes
    return 0

unsafe def checkKProofWithContext (ctx : StmtContext) (modStr stmtPath kind : String)
    (depPaths : List String) (leafPath : String) : IO (UInt32 × Array String) := do
  let mod := modStr.toName
  unless kind == "check" || kind == "refute" || kind == "reduce" do
    return (3, #[s!"kind must be check, refute or reduce, got {kind}"])
  unless isProject mod && !isDefs mod && !ctx.stmtModules.contains mod do
    return formatReject "not-a-project-module" s!"{mod} is not an outside proof module"
  let stmt ← try IO.FS.readFile stmtPath catch e => return (3, #[s!"cannot read statement: {e}"])
  let mut consts : Std.HashMap Name ConstantInfo := {}
  let mut projectModules : Array Name := #[]
  let mut modExtras : Option (Array Name) := none
  let allFiles := depPaths.map (·, false) ++ [(leafPath, true)]
  for (path, isLeaf) in allFiles do
    let raw ← try IO.FS.readBinFile path catch e => return (3, #[s!"cannot read kproof {path}: {e}"])
    let decoded ← match KProof.decodeModule raw with
      | .error msg => return formatReject "kproof" s!"malformed kproof artifact: {msg}"
      | .ok d => pure d
    let m := decoded.module
    if isLeaf && m != mod then
      return formatReject "kproof" s!"kproof declares module {m}, expected {mod}"
    unless isProject m && !isDefs m && !ctx.stmtModules.contains m do
      return formatReject "not-a-project-module" s!"{m} is not an outside project module"
    if projectModules.contains m then
      return formatReject "kproof" s!"duplicate module {m} in kproof bundle"
    projectModules := projectModules.push m
    if isLeaf then
      modExtras := some decoded.extras
    for c in decoded.constants do
      if reserved.isPrefixOf c.name then
        return formatReject "reserved-name" s!"{m} declares {c.name}; names under {reserved} belong to the checker"
      if let some l := ctx.libEnv.find? c.name then
        if sameTheorem c l then continue
        return formatReject "redeclares" s!"{m} declares {c.name}, a name the pinned library or the definitions root already declares. A project module may not declare it again"
      if consts.contains c.name then
        return formatReject "redeclares" s!"{m} redeclares {c.name} already provided by another module"
      consts := consts.insert c.name c
  verifyLoaded ctx mod stmt kind projectModules ctx.defsModules consts modExtras

unsafe def serveKProof : IO UInt32 := do
  let ctx ← match ← loadStmtContext with
    | .error (code, lines) =>
      for l in lines do IO.eprintln l
      return code
    | .ok c => pure c
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStr "READY\n"
  stdout.flush
  repeat do
    let rawLine ← stdin.getLine
    if rawLine.isEmpty then break
    let line := (rawLine.replace "\r" "").replace "\n" ""
    if line.isEmpty then continue
    if line == "QUIT" then break
    let res : UInt32 × Array String ← try
        match line.splitOn "\t" with
        | [modStr, stmtPath, kind, leafPath, depsCsv] =>
          let deps := if depsCsv.isEmpty then [] else depsCsv.splitOn ","
          checkKProofWithContext ctx modStr stmtPath kind deps leafPath
        | [modStr, stmtPath, kind, leafPath] =>
          checkKProofWithContext ctx modStr stmtPath kind [] leafPath
        | _ => pure (3, #["malformed request line"])
      catch e =>
        pure (3, #[s!"checker fault: {e}"])
    stdout.putStr s!"BEGIN_RESULT {res.1} {res.2.size}\n"
    for outLine in res.2 do
      stdout.putStr (outLine ++ "\n")
    stdout.putStr "END_RESULT\n"
    stdout.flush
  return 0

end PEqualNPChecker

unsafe def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["--export-kproof", mod, outPath] =>
      PEqualNPChecker.exportKProofFile mod outPath
    | "--check-kproof" :: mod :: stmt :: kind :: leaf :: deps =>
      match ← PEqualNPChecker.loadStmtContext with
      | .error res => PEqualNPChecker.emitResult res
      | .ok ctx => PEqualNPChecker.emitResult (← PEqualNPChecker.checkKProofWithContext ctx mod stmt kind deps leaf)
    | ["--serve-kproof"] =>
      PEqualNPChecker.serveKProof
    | [mod, stmt, kind] =>
      PEqualNPChecker.run mod stmt kind
    | _ =>
      IO.eprintln "usage: CheckLemma <module> <statement file> <check|refute|reduce> | --export-kproof <module> <out> | --check-kproof <module> <stmt> <kind> <leaf.kproof> [dep.kproof...] | --serve-kproof"
      return 3
  catch e =>
    IO.eprintln s!"checker fault: {e}"
    return 3
