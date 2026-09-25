/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean

/-!
Additional functions to deal with `InfoTree`.
-/

open Lean Elab Meta

namespace Lean.FileMap

/-- Extract the range of a `Syntax` expressed as lines and columns. -/
-- Extracted from the private declaration `Lean.Elab.formatStxRange`,
-- in `Lean.Elab.InfoTree.Main`.
def stxRange (fileMap : FileMap) (stx : Syntax) : Position × Position :=
  let pos    := stx.getPos?.getD 0
  let endPos := stx.getTailPos?.getD pos
  (fileMap.toPosition pos, fileMap.toPosition endPos)

end Lean.FileMap

namespace Lean.Syntax

/-- Check if a `Syntax` is an explicit invocation of the `sorry` tactic. -/
def isSorryTactic (stx : Syntax) : Bool :=
  s!"{stx}" = "(Tactic.tacticSorry \"sorry\")"

/-- Check if a `Syntax` is an explicit `sorry` term. -/
def isSorryTerm (stx : Syntax) : Bool :=
  s!"{stx}" = "(Term.sorry \"sorry\")"

end Lean.Syntax

namespace Lean.Elab

/-- Extract the range of a `Syntax` expressed as lines and columns. -/
-- Extracted from the private declaration `Lean.Elab.formatStxRange`,
-- in `Lean.Elab.InfoTree.Main`.
def stxRange (fileMap : FileMap) (stx : Syntax) : Position × Position :=
  let pos    := stx.getPos?.getD 0
  let endPos := stx.getTailPos?.getD pos
  (fileMap.toPosition pos, fileMap.toPosition endPos)

end Lean.Elab

namespace Lean.Elab.Info

/-- The type of a `Lean.Elab.Info`, as a string. -/
def kind : Info → String
  | .ofTacticInfo         _ => "TacticInfo"
  | .ofTermInfo           _ => "TermInfo"
  | ofPartialTermInfo     _ => "PartialTermInfo"
  | .ofCommandInfo        _ => "CommmandInfo"
  | .ofMacroExpansionInfo _ => "MacroExpansionInfo"
  | .ofOptionInfo         _ => "OptionInfo"
  | .ofFieldInfo          _ => "FieldInfo"
  | .ofCompletionInfo     _ => "CompletionInfo"
  | .ofUserWidgetInfo     _ => "UserWidgetInfo"
  | .ofCustomInfo         _ => "CustomInfo"
  | .ofFVarAliasInfo      _ => "FVarAliasInfo"
  | .ofFieldRedeclInfo    _ => "FieldRedeclInfo"
  | .ofOmissionInfo       _ => "OmissionInfo"
  | .ofChoiceInfo         _ => "ChoiceInfo"

/-- The `Syntax` for a `Lean.Elab.Info`, if there is one. -/
def stx? : Info → Option Syntax
  | .ofTacticInfo         info => info.stx
  | .ofTermInfo           info => info.stx
  | ofPartialTermInfo     info => info.stx
  | .ofCommandInfo        info => info.stx
  | .ofMacroExpansionInfo info => info.stx
  | .ofOptionInfo         info => info.stx
  | .ofFieldInfo          info => info.stx
  | .ofCompletionInfo     info => info.stx
  | .ofUserWidgetInfo     info => info.stx
  | .ofCustomInfo         info => info.stx
  | .ofFVarAliasInfo      _    => none
  | .ofFieldRedeclInfo    info => info.stx
  | .ofOmissionInfo       info => info.stx
  | .ofChoiceInfo         info => info.stx

/-- Is the `Syntax` for this `Lean.Elab.Info` original, or synthetic? -/
def isOriginal (i : Info) : Bool :=
  match i.stx? with
  | none => true   -- Somewhat unclear what to do with `FVarAliasInfo`, so be conservative.
  | some stx => match stx.getHeadInfo with
    | .original .. => true
    | _ => false

end Lean.Elab.Info
namespace Lean.Elab.TacticInfo

/-- Find the name for the outermost `Syntax` in this `TacticInfo`. -/
def name? (t : TacticInfo) : Option Name :=
  match t.stx with
  | Syntax.node _ n _ => some n
  | _ => none

/-- Decide whether a tactic is "substantive",
or is merely a tactic combinator (e.g. `by`, `;`, multiline tactics, parenthesized tactics). -/
def isSubstantive (t : TacticInfo) : Bool :=
  match t.name? with
  | none => false
  | some `null => false
  | some ``cdot => false
  | some ``cdotTk => false
  | some ``Lean.Parser.Term.byTactic => false
  | some ``Lean.Parser.Tactic.tacticSeq => false
  | some ``Lean.Parser.Tactic.tacticSeq1Indented => false
  | some ``Lean.Parser.Tactic.«tactic_<;>_» => false
  | some ``Lean.Parser.Tactic.paren => false
  | _ => true

def getUsedConstantsAsSet (t : TacticInfo) : NameSet :=
  t.goalsBefore
    |>.filterMap t.mctxAfter.getExprAssignmentCore?
    |>.map Expr.getUsedConstantsAsSet
    |>.foldl .union .empty

end Lean.Elab.TacticInfo

namespace Lean.Elab.InfoTree

/--
Keep `.node` nodes and `.hole` nodes satisfying predicates.

Returns a `List InfoTree`, although in most situations this will be a singleton.
-/
partial def filter (p : Info → Bool) (m : MVarId → Bool := fun _ => false) :
    InfoTree → List InfoTree
  | .context ctx tree => tree.filter p m |>.map (.context ctx)
  | .node info children =>
    if p info then
      [.node info (children.toList.map (filter p m)).flatten.toPArray']
    else
      (children.toList.map (filter p m)).flatten
  | .hole mvar => if m mvar then [.hole mvar] else []

/-- Discard all nodes besides `.context` nodes and `TacticInfo` nodes. -/
partial def retainTacticInfo (tree : InfoTree) : List InfoTree :=
  tree.filter fun | .ofTacticInfo _ => true | _ => false

/-- Retain only nodes with "original" syntax. -/
partial def retainOriginal (tree : InfoTree) : List InfoTree :=
  tree.filter Info.isOriginal

/-- Discard all TacticInfo nodes that are tactic combinators or structuring tactics. -/
-- There is considerable grey area here: what to do with `classical`?
partial def retainSubstantive (tree : InfoTree) : List InfoTree :=
  tree.filter fun | .ofTacticInfo i => i.isSubstantive | _ => true

/-- Analogue of `Lean.Elab.InfoTree.findInfo?`, but that returns all results. -/
partial def findAllInfo (t : InfoTree) (ctx? : Option ContextInfo) (p : Info → Bool) :
    List (Info × Option ContextInfo) :=
  match t with
  | context ctx t => t.findAllInfo (ctx.mergeIntoOuter? ctx?) p
  | node i ts  =>
    let info := if p i then [(i, ctx?)] else []
    let rest := ts.toList.flatMap (fun t => t.findAllInfo ctx? p)
    info ++ rest
  | _ => []

/-- Return all `TacticInfo` nodes in an `InfoTree` with "original" syntax,
each equipped with its relevant `ContextInfo`. -/
def findTacticNodes (t : InfoTree) : List (TacticInfo × ContextInfo) :=
  let infos := t.findAllInfo none fun i => match i with
  | .ofTacticInfo i' => i.isOriginal && i'.isSubstantive
  | _ => false
  infos.filterMap fun p => match p with
  | (.ofTacticInfo i, some ctx) => (i, ctx)
  | _ => none

/-- Return all `TacticInfo` nodes in an `InfoTree`
corresponding to explicit invocations of the `sorry` tactic,
each equipped with its relevant `ContextInfo`. -/
def findSorryTacticNodes (t : InfoTree) : List (TacticInfo × ContextInfo) :=
  let infos := t.findAllInfo none fun i => match i with
  | .ofTacticInfo i => i.stx.isSorryTactic && !i.goalsBefore.isEmpty
  | _ => false
  infos.filterMap fun p => match p with
  | (.ofTacticInfo i, some ctx) => (i, ctx)
  | _ => none

/-- Return all `TermInfo` nodes in an `InfoTree`
corresponding to explicit `sorry` terms,
each equipped with its relevant `ContextInfo`. -/
def findSorryTermNodes (t : InfoTree) : List (TermInfo × ContextInfo) :=
  let infos := t.findAllInfo none fun i => match i with
  | .ofTermInfo i => i.stx.isSorryTerm
  | _ => false
  infos.filterMap fun p => match p with
  | (.ofTermInfo i, some ctx) => (i, ctx)
  | _ => none

inductive SorryType
| tactic : MVarId → SorryType
| term : LocalContext → Option Expr → SorryType
deriving Inhabited

/--
Finds all appearances of `sorry` in an `InfoTree`, reporting
* the `ContextInfo` at that point,
* the `MVarId` for a goal that was closed by `sorry`,
  or the `Option Expr` expected type for a term supplied by `sorry`
* and the start and end positions of the `sorry` in the file.
-/
def sorries (t : InfoTree) : List (ContextInfo × SorryType × Position × Position) :=
  (t.findSorryTacticNodes.map fun ⟨i, ctx⟩ =>
    -- HACK: creating a child ngen
    ({ ctx with mctx := i.mctxBefore, ngen := ctx.ngen.mkChild.1 }, .tactic i.goalsBefore.head!,
      stxRange ctx.fileMap i.stx)) ++
  (t.findSorryTermNodes.map fun ⟨i, ctx⟩ =>
    (ctx, .term i.lctx i.expectedType?, stxRange ctx.fileMap i.stx))

def tactics (t : InfoTree) : List (ContextInfo × Syntax × List MVarId × Position × Position × Array Name) :=
    -- HACK: creating a child ngen
  t.findTacticNodes.map fun ⟨i, ctx⟩ =>
    let range := stxRange ctx.fileMap i.stx
    ( { ctx with mctx := i.mctxBefore, ngen := ctx.ngen.mkChild.1 },
      i.stx,
      i.goalsBefore,
      range.fst,
      range.snd,
      i.getUsedConstantsAsSet.toArray )


/-- One source tactic discovered while reconstructing a tactic sequence. -/
structure TacticSequenceNode where
  /-- Unique within this check, even when the same source executes repeatedly. -/
  executionId : Nat
  /-- A checked stage belongs to this specific enclosing execution. -/
  ownerId : Option Nat := none
  ctx : ContextInfo
  info : TacticInfo
  /-- Whether a surrounding combinator permits this tactic to fail. -/
  mayFail : Bool := false

/--
A source-level tactic sequence together with the syntax node that owns it.

Keeping the sequence container is a small extension over mathlib's
`Mathlib.TacticAnalysis.findTacticSeqs`: it preserves the range of an enclosing
`by`, bullet body, or tactic-sequence node for clients that need to reconstruct
nesting without guessing from indentation.
-/
structure TacticSequence where
  ctx : ContextInfo
  stx : Syntax
  tactics : List TacticSequenceNode

/-- One parsed source step in a `calc` block. -/
structure CalcStep where
  stx : Syntax
  proof? : Option Syntax

/-- A parsed `calc` block and its nearest enclosing tactic. -/
structure CalcBlock where
  ctx : ContextInfo
  stx : Syntax
  owner? : Option Syntax
  steps : List CalcStep

private structure TacticSequenceVisitResult where
  tactic? : Option TacticSequenceNode := none
  sequences : List TacticSequence := []
deriving Inhabited

private def isTacticSequenceKind (kind : Name) : Bool :=
  kind == ``Lean.Parser.Tactic.tacticSeq ||
  kind == ``Lean.Parser.Tactic.tacticSeq1Indented ||
  kind == ``Lean.Parser.Term.byTactic

private def isTacticPunctuationKind (kind : Name) : Bool :=
  kind == `«;» ||
  kind == `Lean.cdotTk ||
  kind == `«]» ||
  kind == nullKind ||
  kind == `«by»

private def allowsChildFailure (kind : Name) : Bool :=
  kind == ``Lean.Parser.Tactic.tacticTry_ ||
  kind == ``Lean.Parser.Tactic.anyGoals

private def markSequenceMayFail (sequence : TacticSequence) : TacticSequence :=
  { sequence with
    tactics := sequence.tactics.map fun tactic => { tactic with mayFail := true } }

/--
Traverse an infotree and recover source tactic sequences.

This follows the traversal used by mathlib's
`Mathlib.TacticAnalysis.findTacticSeqs`, adapted to Lean 4.15 and extended to
retain each sequence container's syntax range.
-/
private partial def collectTacticSequences
    (tree : InfoTree) (ctx? : Option ContextInfo)
    (rewriteRules : Array (Syntax × Nat) := #[]) : StateM Nat TacticSequenceVisitResult := do
  match tree with
  | .context ctx tree =>
    collectTacticSequences tree (ctx.mergeIntoOuter? ctx?) rewriteRules
  | .hole _ =>
    return {}
  | .node info children =>
    let executionId ← modifyGet fun next => (next, next + 1)
    -- Remember the execution that owns each multi-rule list before visiting
    -- its children. Source positions identify rules, never their executions.
    let rewriteRules := match info, info.stx? with
      | .ofTacticInfo _, some stx =>
        match stx.getHeadInfo? with
        | some (.original ..) => stx.getArgs.foldl (fun rules arg =>
            if arg.isOfKind ``Lean.Parser.Tactic.rwRuleSeq && arg[1].getArgs.size > 2 then
              rules ++ (arg[1].getArgs.filter (·.isOfKind ``Lean.Parser.Tactic.rwRule)).map
                (fun rule => (rule, executionId))
            else rules) rewriteRules
        | _ => rewriteRules
      | _, _ => rewriteRules
    let childResults ← children.toList.mapM fun child =>
      collectTacticSequences child ctx? rewriteRules
    let childTactics := childResults.filterMap (fun result => result.tactic?)
    let childSequences := childResults.flatMap (fun result => result.sequences)
    match info.stx?, ctx? with
    | some stx, some ctx =>
      let kind := stx.getKind
      let rule := stx[0]
      let owner := if kind == nullKind && rule.isOfKind ``Lean.Parser.Tactic.rwRule then
        rewriteRules.toList.reverse.find? fun (original, _) =>
          original.getPos? == rule.getPos? && original.getTailPos? == rule.getTailPos?
        else none
      if let some (_, ownerId) := owner then
        match info with
        | .ofTacticInfo tacticInfo =>
          -- Lean annotates [rule, comma]. Keep the original rule's range.
          let tactic : TacticSequenceNode := {
            executionId := executionId
            ownerId := some ownerId
            ctx := ctx
            info := { tacticInfo with stx := rule } }
          let sequence := { ctx, stx := rule, tactics := [tactic] : TacticSequence }
          return { sequences := childSequences ++ [sequence] }
        | _ => return { sequences := childSequences }
      else if isTacticSequenceKind kind then
        let sequences :=
          if childTactics.isEmpty && kind == ``Lean.Parser.Term.byTactic then
            match childSequences.reverse with
            | [] => []
            | sequence :: preceding => preceding.reverse ++ [{ sequence with ctx, stx }]
          else if childTactics.isEmpty then childSequences
          else childSequences ++ [{ ctx, stx, tactics := childTactics }]
        return { sequences }
      else
        match stx.getHeadInfo? with
        | some (.original ..) =>
          if isTacticPunctuationKind kind then
            return { sequences := childSequences }
          else if kind == ``Lean.Parser.Tactic.withAnnotateState then
            return { tactic? := childTactics.head?, sequences := childSequences }
          else
            match info with
            | .ofTacticInfo tacticInfo =>
              let sequences :=
                if allowsChildFailure kind then childSequences.map markSequenceMayFail
                else childSequences
              return { tactic? := some { executionId, ctx, info := tacticInfo }, sequences }
            | _ => return { sequences := childSequences }
        | _ => return { sequences := childSequences }
    | _, _ => return { sequences := childSequences }

/-- Number executions across every tree in one response, preserving stage ownership. -/
def tacticSequences (trees : List InfoTree) : List TacticSequence :=
  ((trees.mapM fun tree => do
    return (← collectTacticSequences tree none).sequences).run' 0).flatten

private def unpackCalcSteps (steps : TSyntax ``Lean.calcSteps) : Option (List CalcStep) :=
  match steps with
  | `(calcSteps|
      $step0:calcFirstStep
      $rest*) =>
    let first? := match step0 with
      | `(calcFirstStep| $_:term := $proof:term) => some { stx := step0, proof? := some proof }
      | `(calcFirstStep| $_:term) => some { stx := step0, proof? := none }
      | _ => none
    let rest := rest.toList.filterMap fun (step : TSyntax ``Lean.calcStep) =>
      match step with
      | `(calcStep| $_:term := $proof:term) => some { stx := step.raw, proof? := some proof.raw }
      | _ => none
    first?.map fun first => first :: rest
  | _ => none

private def unpackCalc? (stx : Syntax) : Option (List CalcStep) :=
  match stx with
  | `(term| calc $steps:calcSteps) => unpackCalcSteps steps
  | `(tactic| calc $steps:calcSteps) => unpackCalcSteps steps
  | _ => none

/-- Traverse an infotree and recover original term- and tactic-level `calc` blocks. -/
private partial def collectCalcBlocks
    (tree : InfoTree) (ctx? : Option ContextInfo) (owner? : Option Syntax) : List CalcBlock :=
  match tree with
  | .context ctx tree =>
    collectCalcBlocks tree (ctx.mergeIntoOuter? ctx?) owner?
  | .hole _ =>
    []
  | .node info children =>
    let owner? := match info with
      | .ofTacticInfo tacticInfo => some tacticInfo.stx
      | _ => owner?
    let childBlocks := children.toList.flatMap fun child =>
      collectCalcBlocks child ctx? owner?
    match info.stx?, ctx? with
    | some stx, some ctx =>
      match stx.getHeadInfo?, unpackCalc? stx with
      | some (.original ..), some steps =>
        childBlocks ++ [{ ctx, stx, owner?, steps }]
      | _, _ => childBlocks
    | _, _ => childBlocks

/-- Return all original source `calc` blocks contained in an infotree. -/
def calcBlocks (tree : InfoTree) : List CalcBlock :=
  collectCalcBlocks tree none none


end Lean.Elab.InfoTree

namespace Lean.Elab.TacticInfo

/-- Return the range of the tactic, as a pair of file positions. -/
def range (info : TacticInfo) (ctx : ContextInfo) : Position × Position := ctx.fileMap.stxRange info.stx

/-- Pretty print a tactic. -/
def pp (info : TacticInfo) (ctx : ContextInfo) : IO Format :=
  ctx.runMetaM {} try
    Lean.PrettyPrinter.ppTactic ⟨info.stx⟩
  catch _ =>
    pure "<failed to pretty print>"

open Meta

/-- Run a tactic on the goals stored in a `TacticInfo`. -/
def runMetaMGoalsBefore (info : TacticInfo) (ctx : ContextInfo) (x : List MVarId → MetaM α) : IO α := do
  ctx.runMetaM {} <| Meta.withMCtx info.mctxBefore <| x info.goalsBefore

/-- Run a tactic on the after goals stored in a `TacticInfo`. -/
def runMetaMGoalsAfter (info : TacticInfo) (ctx : ContextInfo) (x : List MVarId → MetaM α) : IO α := do
  ctx.runMetaM {} <| Meta.withMCtx info.mctxAfter <| x info.goalsAfter

/-- Run a tactic on the main goal stored in a `TacticInfo`. -/
def runMetaM (info : TacticInfo) (ctx : ContextInfo) (x : MVarId → MetaM α) : IO α := do
  match info.goalsBefore.head? with
  | none => throw <| IO.userError s!"No goals at {← info.pp ctx}"
  | some g => info.runMetaMGoalsBefore ctx fun _ => do g.withContext <| x g

def mainGoal (info : TacticInfo) (ctx : ContextInfo) : IO Expr :=
  info.runMetaM ctx (fun g => do instantiateMVars (← g.getType))

def formatMainGoal (info : TacticInfo) (ctx : ContextInfo) : IO Format :=
  info.runMetaM ctx (fun g => do ppExpr (← instantiateMVars (← g.getType)))

def goalState (info : TacticInfo) (ctx : ContextInfo) : IO (List Format) := do
  info.runMetaMGoalsBefore ctx (fun gs => gs.mapM fun g => do Meta.ppGoal g)

def goalStateAfter (info : TacticInfo) (ctx : ContextInfo) : IO (List Format) := do
  info.runMetaMGoalsAfter ctx (fun gs => gs.mapM fun g => do Meta.ppGoal g)

def ppExpr (info : TacticInfo) (ctx : ContextInfo) (e : Expr) : IO Format :=
  info.runMetaM ctx (fun _ => do Meta.ppExpr (← instantiateMVars e))

end Lean.Elab.TacticInfo

namespace Lean.Elab.InfoTree

/--
Finds all tactic invocations in an `InfoTree`,
ignoring structuring tactics (e.g. `by`, `;`, multiline tactics, parenthesized tactics).
-/
def substantiveTactics (t : InfoTree) : List (TacticInfo × ContextInfo) :=
  t.findTacticNodes.filter fun i => i.1.isSubstantive

end Lean.Elab.InfoTree
