import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21317

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [7, 8]⟩,
      ⟨GateOp.and, [0, 9]⟩,
      ⟨GateOp.or, [5, 2]⟩,
      ⟨GateOp.or, [3, 6]⟩,
      ⟨GateOp.or, [11, 12]⟩,
      ⟨GateOp.or, [4, 1]⟩,
      ⟨GateOp.or, [13, 7]⟩,
      ⟨GateOp.and, [15, 14]⟩,
      ⟨GateOp.and, [11, 12]⟩,
      ⟨GateOp.or, [16, 10]⟩,
      ⟨GateOp.or, [17, 18]⟩
    ],
    output := 19 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 5) => (103896 : ℕ).testBit (5 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_21317

theorem PEqualNP.Outside.L_meta_21317 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103896 : ℕ).testBit (5 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_21317.ckt, PEqualNP.Outside.L_meta_21317.mono, by decide, PEqualNP.Outside.L_meta_21317.rep⟩
