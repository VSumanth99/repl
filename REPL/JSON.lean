/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Data.Json
import Lean.Message
import Lean.Elab.InfoTree.Main

open Lean Elab InfoTree

namespace REPL

structure CommandOptions where
  allTactics : Option Bool := none
  /-- Export source-level tactic sequences with their proof states. -/
  tacticSequences : Option Bool := none
  /-- Export enabled Lean traces as structured automation events. -/
  automationEvents : Option Bool := none
  /--
  Should be "full", "tactics", "original", or "substantive".
  Anything else is ignored.
  -/
  infotree : Option String

/-- Run Lean commands.
If `env = none`, starts a new session (in which you can use `import`).
If `env = some n`, builds on the existing environment `n`.
-/
structure Command extends CommandOptions where
  env : Option Nat
  cmd : String
deriving ToJson, FromJson

/-- Process a Lean file in a fresh environment. -/
structure File extends CommandOptions where
  path : System.FilePath
deriving FromJson

/--
Run a tactic in a proof state.
-/
structure ProofStep where
  proofState : Nat
  tactic : String
deriving ToJson, FromJson

/-- Line and column information for error messages and sorries. -/
structure Pos where
  line : Nat
  column : Nat
deriving ToJson, FromJson

/-- Severity of a message. -/
inductive Severity
  | trace | info | warning | error
deriving ToJson, FromJson

/-- A Lean message. -/
structure Message where
  pos : Pos
  endPos : Option Pos
  severity : Severity
  data : String
deriving ToJson, FromJson

/-- Construct the JSON representation of a Lean message. -/
def Message.of (m : Lean.Message) : IO Message := do
  let data := (← m.data.toString).trimAscii.toString
  -- Existing Kimina clients recognize this warning verbatim when rejecting sorry.
  let data := if m.severity == .warning && data == "declaration uses `sorry`" then
      "declaration uses 'sorry'"
    else data
  pure <|
  { pos := ⟨m.pos.line, m.pos.column⟩,
    endPos := m.endPos.map fun p => ⟨p.line, p.column⟩,
    severity := match m.severity with
    | .information => .info
    | .warning => .warning
    | .error => .error,
    data }

/-- One structured event emitted by an enabled Lean automation trace. -/
structure AutomationEvent where
  kind : Name
  pos : Pos
  endPos : Option Pos
  message : String
  children : List AutomationEvent := []
deriving ToJson, FromJson

/--
Collect trace nodes without parsing their rendered `[trace.class]` prefixes.

Lean stores trace messages as a `MessageData` tree. `addTraceAsMessages` joins
the traces at each position with `MessageData.joinSep`, which builds a deep
`compose` chain whose length is the number of traces at that position. Recursing
one stack frame per `compose` node overflows the REPL stack on automation-heavy
proofs, so this traversal flattens the tree with an explicit worklist instead.
-/
private partial def AutomationEvent.fromMessageData
    (pos : Pos) (endPos : Option Pos) (namingContext : NamingContext)
    (messageContext : Option MessageDataContext) : MessageData → IO (List AutomationEvent)
  | data => traverse [(namingContext, messageContext, data)]
where
  /-- Visit one worklist of sibling messages iteratively, preserving left-to-right order. -/
  traverse (work : List (NamingContext × Option MessageDataContext × MessageData)) :
      IO (List AutomationEvent) := do
    let mut stack := work
    let mut events : List AutomationEvent := []
    while !stack.isEmpty do
      match stack with
      | [] => pure ()
      | head :: tail =>
        stack := tail
        let namingContext := head.1
        let messageContextAndNode := head.2
        let messageContext := messageContextAndNode.1
        let node := messageContextAndNode.2
        match node with
        | .compose left right =>
            stack := (namingContext, messageContext, left) ::
              (namingContext, messageContext, right) :: stack
        | .withContext ctx data =>
            stack := (namingContext, some ctx, data) :: stack
        | .withNamingContext ctx data =>
            stack := (ctx, messageContext, data) :: stack
        | .nest _ data | .group data | .tagged _ data | .ofWidget _ data
          | .ofOriginatingSyntax _ data =>
            stack := (namingContext, messageContext, data) :: stack
        | .ofLazy render _ => do
            let dynamic ← render (messageContext.map (MessageData.mkPPContext namingContext))
            if let some data := dynamic.get? MessageData then
              stack := (namingContext, messageContext, data) :: stack
        | .trace traceData header children => do
            if traceData.cls.isAnonymous then
              -- Lean 4.33 groups traces at a position in a synthetic root node.
              stack := children.toList.map (fun child => (namingContext, messageContext, child)) ++ stack
            else
              let message := (← MessageData.formatAux namingContext messageContext header).pretty.trim
              let childEvents ← traverse <|
                children.toList.map fun child => (namingContext, messageContext, child)
              events := { kind := traceData.cls, pos, endPos, message, children := childEvents } :: events
        | .ofFormatWithInfos _ | .ofGoal _ =>
            pure ()
    pure events.reverse

/-- Extract every structured automation event contained in a Lean message. -/
def AutomationEvent.ofMessage (message : Lean.Message) : IO (List AutomationEvent) :=
  fromMessageData
    ⟨message.pos.line, message.pos.column⟩
    (message.endPos.map fun pos => ⟨pos.line, pos.column⟩)
    { currNamespace := Name.anonymous, openDecls := [] }
    none
    message.data

/-- A Lean `sorry`. -/
structure Sorry where
  pos : Pos
  endPos : Pos
  goal : String
  /--
  The index of the proof state at the sorry.
  You can use the `ProofStep` instruction to run a tactic at this state.
  -/
  proofState : Option Nat
deriving FromJson

instance : ToJson Sorry where
  toJson r := Json.mkObj <| .flatten [
    [("goal", r.goal)],
    [("proofState", toJson r.proofState)],
    if r.pos.line ≠ 0 then [("pos", toJson r.pos)] else [],
    if r.endPos.line ≠ 0 then [("endPos", toJson r.endPos)] else [],
  ]

/-- Construct the JSON representation of a Lean sorry. -/
def Sorry.of (goal : String) (pos endPos : Lean.Position) (proofState : Option Nat) : Sorry :=
  { pos := ⟨pos.line, pos.column⟩,
    endPos := ⟨endPos.line, endPos.column⟩,
    goal,
    proofState }

structure Tactic where
  pos : Pos
  endPos : Pos
  goals : String
  tactic : String
  proofState : Option Nat
  usedConstants : Array Name
deriving ToJson, FromJson

/-- Construct the JSON representation of a Lean tactic. -/
def Tactic.of (goals tactic : String) (pos endPos : Lean.Position) (proofState : Option Nat) (usedConstants : Array Name) : Tactic :=
  { pos := ⟨pos.line, pos.column⟩,
    endPos := ⟨endPos.line, endPos.column⟩,
    goals,
    tactic,
    proofState,
    usedConstants }

/-- One tactic in a source-level tactic sequence. -/
structure TacticSequenceEntry where
  name : Option Name
  pos : Pos
  endPos : Pos
  goalsBefore : List String
  goalsAfter : List String
  tactic : String
  mayFail : Bool
deriving ToJson, FromJson

/-- A source tactic sequence and the syntax container that owns it. -/
structure TacticSequence where
  name : Name
  synthetic : Bool
  pos : Pos
  endPos : Pos
  tactics : List TacticSequenceEntry
deriving ToJson, FromJson

/-- One source step in a term- or tactic-level `calc` block. -/
structure CalcStep where
  pos : Pos
  endPos : Pos
  proofPos : Option Pos
  proofEndPos : Option Pos
deriving ToJson, FromJson

/-- Source ranges for a `calc` block and the tactic that owns it, if any. -/
structure CalcBlock where
  name : Name
  pos : Pos
  endPos : Pos
  ownerPos : Option Pos
  ownerEndPos : Option Pos
  steps : List CalcStep
deriving ToJson, FromJson

/--
A response to a Lean command.
`env` can be used in later calls, to build on the stored environment.
-/
structure CommandResponse where
  env : Nat
  messages : List Message := []
  automationEvents : List AutomationEvent := []
  sorries : List Sorry := []
  tactics : List Tactic := []
  tacticSequences : List TacticSequence := []
  calcBlocks : List CalcBlock := []
  infotree : Option Json := none
deriving FromJson

def Json.nonemptyList [ToJson α] (k : String) : List α → List (String × Json)
  | [] => []
  | l  => [⟨k, toJson l⟩]

instance : ToJson CommandResponse where
  toJson r := Json.mkObj <| .flatten [
    [("env", r.env)],
    Json.nonemptyList "messages" r.messages,
    Json.nonemptyList "automationEvents" r.automationEvents,
    Json.nonemptyList "sorries" r.sorries,
    Json.nonemptyList "tactics" r.tactics,
    Json.nonemptyList "tacticSequences" r.tacticSequences,
    Json.nonemptyList "calcBlocks" r.calcBlocks,
    match r.infotree with | some j => [("infotree", j)] | none => []
  ]

/--
A response to a Lean tactic.
`proofState` can be used in later calls, to run further tactics.
-/
structure ProofStepResponse where
  proofState : Nat
  goals : List String
  messages : List Message := []
  sorries : List Sorry := []
  traces : List String
deriving ToJson, FromJson

instance : ToJson ProofStepResponse where
  toJson r := Json.mkObj <| .flatten [
    [("proofState", r.proofState)],
    [("goals", toJson r.goals)],
    Json.nonemptyList "messages" r.messages,
    Json.nonemptyList "sorries" r.sorries,
    Json.nonemptyList "traces" r.traces
  ]

/-- Json wrapper for an error. -/
structure Error where
  message : String
deriving ToJson, FromJson

structure PickleEnvironment where
  env : Nat
  pickleTo : System.FilePath
deriving ToJson, FromJson

structure UnpickleEnvironment where
  unpickleEnvFrom : System.FilePath
deriving ToJson, FromJson

structure PickleProofState where
  proofState : Nat
  pickleTo : System.FilePath
deriving ToJson, FromJson

structure UnpickleProofState where
  unpickleProofStateFrom : System.FilePath
  env : Option Nat
deriving ToJson, FromJson

end REPL
