import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22362

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [8, 2]⟩,
      ⟨GateOp.or, [3, 10]⟩,
      ⟨GateOp.or, [7, 0]⟩,
      ⟨GateOp.or, [1, 4]⟩,
      ⟨GateOp.or, [12, 6]⟩,
      ⟨GateOp.and, [5, 3]⟩,
      ⟨GateOp.or, [9, 10]⟩,
      ⟨GateOp.or, [3, 12]⟩,
      ⟨GateOp.or, [11, 14]⟩,
      ⟨GateOp.and, [18, 13]⟩,
      ⟨GateOp.and, [14, 16]⟩,
      ⟨GateOp.or, [20, 19]⟩,
      ⟨GateOp.or, [21, 15]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (841521 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22362

theorem PEqualNP.Outside.L_meta_22362 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841521 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22362.ckt, PEqualNP.Outside.L_meta_22362.mono, by decide, PEqualNP.Outside.L_meta_22362.rep⟩
