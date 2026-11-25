import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7840_1
    (profile :
      have G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b : Fin 42 =>
        a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      ∀ C : PEqualNP.AndCount.AndCountCircuit 42, C.WellFormed → C.Computes G → C.outVars = ∅ →
        (∀ i : Fin C.size, ∀ v : Fin 42, C.gateVal {v} i = false) →
        (∀ i : Fin C.size, Disjoint (C.leftVars i) (C.rightVars i)) → C.size ≤ 20 →
        19 ≤ C.size ∧
          (∀ v : Fin 42,
            {i : Fin C.size | v ∈ C.leftVars i ∨ v ∈ C.rightVars i}.ncard + 16 ≤ C.size) ∧
          ∀ p l : Fin 42, p.val < 21 → 21 ≤ l.val → ¬ G.Adj p l →
            {i : Fin C.size |
              p ∈ C.leftVars i ∨ p ∈ C.rightVars i ∨
              l ∈ C.leftVars i ∨ l ∈ C.rightVars i}.ncard + 14 ≤ C.size)
    (size19 :
      have G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b : Fin 42 =>
        a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      ∀ C : PEqualNP.AndCount.AndCountCircuit 42, C.WellFormed → C.Computes G → C.outVars = ∅ →
        (∀ i : Fin C.size, ∀ v : Fin 42, C.gateVal {v} i = false) →
        (∀ i : Fin C.size, Disjoint (C.leftVars i) (C.rightVars i)) → C.size = 19 →
        (∀ v : Fin 42,
          {i : Fin C.size | v ∈ C.leftVars i ∨ v ∈ C.rightVars i}.ncard ≤ 3) →
        (∀ p l : Fin 42, p.val < 21 → 21 ≤ l.val → ¬ G.Adj p l →
          {i : Fin C.size |
            p ∈ C.leftVars i ∨ p ∈ C.rightVars i ∨
            l ∈ C.leftVars i ∨ l ∈ C.rightVars i}.ncard ≤ 5) → False)
    (size20 :
      have G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b : Fin 42 =>
        a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      ∀ C : PEqualNP.AndCount.AndCountCircuit 42, C.WellFormed → C.Computes G → C.outVars = ∅ →
        (∀ i : Fin C.size, ∀ v : Fin 42, C.gateVal {v} i = false) →
        (∀ i : Fin C.size, Disjoint (C.leftVars i) (C.rightVars i)) → C.size = 20 →
        (∀ v : Fin 42,
          {i : Fin C.size | v ∈ C.leftVars i ∨ v ∈ C.rightVars i}.ncard ≤ 4) →
        (∀ p l : Fin 42, p.val < 21 → 21 ≤ l.val → ¬ G.Adj p l →
          {i : Fin C.size |
            p ∈ C.leftVars i ∨ p ∈ C.rightVars i ∨
            l ∈ C.leftVars i ∨ l ∈ C.rightVars i}.ncard ≤ 6) → False) :
    have G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b : Fin 42 =>
      a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
    ∀ C : PEqualNP.AndCount.AndCountCircuit 42, C.WellFormed → C.Computes G → C.outVars = ∅ →
      (∀ i : Fin C.size, ∀ v : Fin 42, C.gateVal {v} i = false) →
      (∀ i : Fin C.size, Disjoint (C.leftVars i) (C.rightVars i)) →
      (∃ i : Fin C.size, ∃ a ∈ C.leftVars i, ∃ b ∈ C.rightVars i, ¬ G.Adj a b) →
      21 ≤ C.size := by
  dsimp only at profile size19 size20 ⊢
  intro C hWF hComp hOut hSingle hDisjoint _
  by_contra hSmall
  have h20 : C.size ≤ 20 := by omega
  obtain ⟨h19, hVertex, hPair⟩ := profile C hWF hComp hOut hSingle hDisjoint h20
  have hCases : C.size = 19 ∨ C.size = 20 := by omega
  rcases hCases with hs | hs
  · apply size19 C hWF hComp hOut hSingle hDisjoint hs
    · intro v
      have hv := hVertex v
      omega
    · intro p l hp hl hn
      have hpl := hPair p l hp hl hn
      omega
  · apply size20 C hWF hComp hOut hSingle hDisjoint hs
    · intro v
      have hv := hVertex v
      omega
    · intro p l hp hl hn
      have hpl := hPair p l hp hl hn
      omega
