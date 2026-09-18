import Construction.Simulator.MemoryLayout
import Construction.Simulator.OnlineInput
import Construction.Simulator.OutputTargets
import Construction.Simulator.EncLink
import Proof.Privacy.Simulator.Arithmetic.OnlineSamplingCode
import Proof.Privacy.Simulator.Arithmetic.SelectedLabelStoreMachine
import Proof.Privacy.Simulator.Arithmetic.RetargetSchedule
import Proof.Privacy.Simulator.Arithmetic.GateSchedule

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
noncomputable section
attribute [local irreducible] curveGatePlan pointGatePlan

/-- Each online buffer follows the sampled offline words. -/
def onlineInputBase : Nat := privateBase + 917470
def onlineSampleBase : Nat := privateBase + 917475
def onlineTargetBase : Nat := privateBase + 917843
def onlineOriginalBase : Nat := privateBase + 918119
def onlineLinkedBase : Nat := privateBase + 918627

/-- Each setup block installs the exact pointers used by its next proved component. -/
def onlineInputSetup : List LinearInstruction := [.constant 10 (BitVec.ofNat 256 onlineInputBase)]
def onlineOriginalSetup : List LinearInstruction :=
  [.constant 11 (BitVec.ofNat 256 privateBase), .constant 12 (BitVec.ofNat 256 onlineInputBase),
    .constant 14 (BitVec.ofNat 256 onlineOriginalBase)]
def onlineSampleSetup : List LinearInstruction := [.constant 10 (BitVec.ofNat 256 onlineSampleBase)]
def onlineTargetSetup : List LinearInstruction :=
  [.constant 10 (BitVec.ofNat 256 (onlineSampleBase + 92)), .constant 11 (BitVec.ofNat 256 onlineInputBase),
    .constant 14 (BitVec.ofNat 256 onlineSampleBase), .constant 13 (BitVec.ofNat 256 onlineTargetBase)]
def onlineRetargetSetup : List LinearInstruction :=
  [.constant 11 (BitVec.ofNat 256 privateBase), .constant 12 (BitVec.ofNat 256 onlineInputBase),
    .constant 14 (BitVec.ofNat 256 onlineTargetBase)]
def onlineLinkSetup : List LinearInstruction :=
  [.constant 11 (BitVec.ofNat 256 onlineOriginalBase), .constant 14 (BitVec.ofNat 256 onlineLinkedBase),
    .constant 0 (BitVec.ofNat 256 onlineInputBase), .load 12 0,
    .constant 0 (BitVec.ofNat 256 (onlineInputBase + 1)), .load 13 0,
    .constant 0 (BitVec.ofNat 256 privateBase), .load 8 0]
def onlinePointSetup : List LinearInstruction :=
  [.constant 11 (BitVec.ofNat 256 privateBase), .constant 12 (BitVec.ofNat 256 onlineInputBase),
    .constant 14 (BitVec.ofNat 256 onlineLinkedBase)]
def onlineLabelSetup : List LinearInstruction :=
  [.constant 11 (BitVec.ofNat 256 privateBase), .constant 12 (BitVec.ofNat 256 onlineInputBase)]

/-- Each local return maps directly to its next global instruction. -/
def onlineBodyLabels (start length : Nat) (inside : start + length ≤ 317804843)
    (normal : Fin 317804845) (pc : Nat) : Fin 317804845 :=
  if active : pc < length then ⟨start + pc, by omega⟩ else normal

/-- A sampler cutoff maps to the shared cutoff exit. -/
def onlineBranchLabels (start length : Nat) (inside : start + length ≤ 317804843)
    (normal : Fin 317804845) (pc : Nat) : Fin 317804845 :=
  if active : pc < length then ⟨start + pc, by omega⟩
  else if pc = length then normal else 317804844

private opaque onlineCurvePackage (attempts : Nat) :
    {code : Vector (Instruction 1315722) 1315722 // code = (gateLoop curveGatePlan attempts (by decide)).code} :=
  ⟨(gateLoop curveGatePlan attempts (by decide)).code, rfl⟩
private opaque onlinePointPackage (attempts : Nat) :
    {code : Vector (Instruction 314720226) 314720226 // code = (gateLoop pointGatePlan attempts (by decide)).code} :=
  ⟨(gateLoop pointGatePlan attempts (by decide)).code, rfl⟩
def onlineCurveCode (attempts : Nat) : Vector (Instruction 1315722) 1315722 := (onlineCurvePackage attempts).val
def onlinePointCode (attempts : Nat) : Vector (Instruction 314720226) 314720226 := (onlinePointPackage attempts).val
theorem onlineCurveCode_eq (attempts : Nat) : onlineCurveCode attempts = (gateLoop curveGatePlan attempts (by decide)).code :=
  (onlineCurvePackage attempts).property
theorem onlinePointCode_eq (attempts : Nat) : onlinePointCode attempts = (gateLoop pointGatePlan attempts (by decide)).code :=
  (onlinePointPackage attempts).property

/-- The online table includes input, private arithmetic, oracle programming, and final labels.
The valid path runs the label link before both fixed-gate phases.
The absent-output path runs only the curve phase.
Every sampler cutoff reaches the separate final cutoff label. -/
def onlineInstruction (attempts : Nat) (pc : Fin 317804845) : Instruction 317804845 :=
  if block : pc.val < 1 then
    (onlineInputSetup[pc.val]'(by change pc.val < 1; omega)).emit ⟨pc.val + 1, by omega⟩
  else if block : pc.val < 98 then
    relocate (fun label => onlineBodyLabels 1 97 (by decide) 98 label.val)
      (onlineInput.code[pc.val - 1]'(by change pc.val - 1 < 98; omega))
  else if block : pc.val < 101 then
    (onlineOriginalSetup[pc.val - 98]'(by change pc.val - 98 < 3; omega)).emit ⟨pc.val + 1, by omega⟩
  else if block : pc.val < 7213 then
    (selectedLabelStoreCode[pc.val - 101]'(by rw [selectedLabelStoreCode_length]; omega)).emit ⟨pc.val + 1, by omega⟩
  else if block : pc.val < 13618 then
    (retargetCurveCode[pc.val - 7213]'(by rw [retargetCurveCode_length]; omega)).emit ⟨pc.val + 1, by omega⟩
  else if block : pc.val < 13621 then
    match pc.val with
    | 13618 => .constant 0 (BitVec.ofNat 256 (onlineInputBase + 2)) 13619
    | 13619 => .load 0 0 13620
    | _ => .branch 0 1568228 13621
  else if block : pc.val < 13622 then
    (onlineSampleSetup[pc.val - 13621]'(by change pc.val - 13621 < 1; omega)).emit ⟨pc.val + 1, by omega⟩
  else if block : pc.val < 22490 then
    relocate (fun label => onlineBodyLabels 13622 8868 (by decide) 22490 label.val)
      ((onlineSampling attempts).code[pc.val - 13622]'(by change pc.val - 13622 < 8869; omega))
  else if block : pc.val < 22494 then
    (onlineTargetSetup[pc.val - 22490]'(by change pc.val - 22490 < 4; omega)).emit ⟨pc.val + 1, by omega⟩
  else if block : pc.val < 26829 then
    relocate (fun label => onlineBodyLabels 22494 4335 (by decide) 26829 label.val)
      (outputTargetsMachine.code[pc.val - 22494]'(by change pc.val - 22494 < 4336; omega))
  else if block : pc.val < 26832 then
    (onlineRetargetSetup[pc.val - 26829]'(by change pc.val - 26829 < 3; omega)).emit ⟨pc.val + 1, by omega⟩
  else if block : pc.val < 1560754 then
    (retargetPointCode[pc.val - 26832]'(by rw [retargetPointCode_length]; omega)).emit ⟨pc.val + 1, by omega⟩
  else if block : pc.val < 1560762 then
    (onlineLinkSetup[pc.val - 1560754]'(by change pc.val - 1560754 < 8; omega)).emit ⟨pc.val + 1, by omega⟩
  else if block : pc.val < 1568228 then
    relocate (fun label => onlineBranchLabels 1560762 7466 (by decide) 1568228 label.val)
      ((encLink attempts).code[pc.val - 1560762]'(by change pc.val - 1560762 < 7468; omega))
  else if block : pc.val < 1568231 then
    (onlineOriginalSetup[pc.val - 1568228]'(by change pc.val - 1568228 < 3; omega)).emit ⟨pc.val + 1, by omega⟩
  else if block : pc.val < 2883951 then
    relocate (fun label => onlineBranchLabels 1568231 1315720 (by decide) 2883951 label.val)
      ((onlineCurveCode attempts)[pc.val - 1568231]'(by omega))
  else if block : pc.val < 2883954 then
    match pc.val with
    | 2883951 => .constant 0 (BitVec.ofNat 256 (onlineInputBase + 2)) 2883952
    | 2883952 => .load 0 0 2883953
    | _ => .branch 0 317604181 2883954
  else if block : pc.val < 2883957 then
    (onlinePointSetup[pc.val - 2883954]'(by change pc.val - 2883954 < 3; omega)).emit ⟨pc.val + 1, by omega⟩
  else if block : pc.val < 317604181 then
    relocate (fun label => onlineBranchLabels 2883957 314720224 (by decide) 317604181 label.val)
      ((onlinePointCode attempts)[pc.val - 2883957]'(by omega))
  else if block : pc.val < 317604183 then
    (onlineLabelSetup[pc.val - 317604181]'(by change pc.val - 317604181 < 2; omega)).emit ⟨pc.val + 1, by omega⟩
  else if block : pc.val < 317804843 then
    (selectedLabelsCode[pc.val - 317604183]'(by rw [selectedLabelsCode_length]; omega)).emit ⟨pc.val + 1, by omega⟩
  else .halt

/-- The fixed table retains its symbolic instruction function. -/
private opaque onlineMachineCodePackage (attempts : Nat) :
    {code : Vector (Instruction 317804845) 317804845 // code = Vector.ofFn (onlineInstruction attempts)} :=
  ⟨Vector.ofFn (onlineInstruction attempts), rfl⟩
def onlineMachineCode (attempts : Nat) : Vector (Instruction 317804845) 317804845 :=
  (onlineMachineCodePackage attempts).val

/-- Each table lookup selects one instruction without expanding the table. -/
theorem onlineMachineCode_get (attempts index : Nat) (inside : index < 317804845) :
    (onlineMachineCode attempts)[index] = onlineInstruction attempts ⟨index, inside⟩ := by
  rw [onlineMachineCode, (onlineMachineCodePackage attempts).property, Vector.getElem_ofFn]

/-- The machine keeps its fixed table size separate from its symbolic instruction code. -/
abbrev onlineMachine (attempts : Nat) : Machine := ⟨317804844, onlineMachineCode attempts, by decide⟩

end
end Kriterion.ArgoMAC.ArithmeticSimulator
