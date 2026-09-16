import Proof.ConditionalDisclosureCurve
import Proof.Privacy.Distribution.GateProgrammingDistribution
import Proof.Privacy.Programming.Gate

namespace Kriterion.ConditionalDisclosure

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal

namespace CurveSource

/-- The curve-only disclosure source has one bucket use at each public index. -/
theorem bucket_use_subsingleton (source : CurveMaskSample) (inputKey : InputMacKey)
    (lifts : Gate → FullHashLift) (index : Pipeline.FixedKeyIndex) :
    Subsingleton (RawBucketUse (prescription source inputKey lifts) index) :=
  bucket_subsingleton source inputKey lifts index

/-- The fixed curve source uses five adaptor families over 254 coordinate bits. -/
theorem gate_count : Fintype.card Gate = 1270 := gate_card

/-- Its raw source occupies all five pRPM slots for each curve adaptor bit. -/
theorem source_slot_count : Pipeline.curveBucketCount = 6350 :=
  Pipeline.curveBucketCountValue

end CurveSource

theorem curve_schedule_directive_count (request : CurveGateRequest)
    (input : AffineInput) (inputMac : InputMac) :
    (request.schedule input inputMac).length = 1270 := by
  rw [CurveGateRequest.schedule_length]
  norm_num [coordinateBitCount]

theorem gateProgramRecords_length (schedule : List GateDirective) :
    (gateProgramRecords schedule).length = gateScheduleActiveSlotCount schedule := by
  induction schedule with
  | nil => simp [gateProgramRecords, gateScheduleActiveSlotCount]
  | cons directive remaining ih =>
    cases bit : directive.bit <;>
      simp [gateProgramRecords, gateScheduleActiveSlotCount, GateDirective.programRecords,
        GateDirective.activeSlotCount, bit] at ih ⊢ <;> omega

theorem curve_schedule_program_pairs_le (request : CurveGateRequest)
    (input : AffineInput) (inputMac : InputMac) :
    (gateProgramRecords (request.schedule input inputMac)).length ≤ 3810 := by
  rw [gateProgramRecords_length]
  have bound := gateScheduleActiveSlotCount_le (request.schedule input inputMac)
  have count := curve_schedule_directive_count request input inputMac
  omega

end Kriterion.ConditionalDisclosure
