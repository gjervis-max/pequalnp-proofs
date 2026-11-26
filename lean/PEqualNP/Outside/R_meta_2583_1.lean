import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_2583_1
    (hbudget : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m))
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (p q : Fin n) (l k : Fin m), p ≠ q → l ≠ k →
        ¬((p,l) ∈ E ∧ (p,k) ∈ E ∧ (q,l) ∈ E ∧ (q,k) ∈ E)) →
      PEqualNP.TopForm.IsAO2 (n + m) C →
      (∀ z, PEqualNP.MetaComplexity.circuitFun (n + m) C z =
        decide (∃ p l, (p,l) ∈ E ∧ z (Fin.castAdd m p) = true ∧
          z (Fin.natAdd n l) = true)) →
      ∃ (A : Finset (Fin n)) (B : Finset (Fin m)),
        (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) ∧
        E.card + A.card + B.card - 1 ≤ C.size)
    (hstar : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m))
      (A : Finset (Fin n)) (B : Finset (Fin m)),
      (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 (n + m) D ∧
        D.size ≤ E.card + A.card + B.card - 1 ∧
        (∀ z, PEqualNP.MetaComplexity.circuitFun (n + m) D z =
          decide (∃ p l, (p,l) ∈ E ∧ z (Fin.castAdd m p) = true ∧
            z (Fin.natAdd n l) = true)) ∧
        PEqualNP.ReadK.IsReadK (n + m) D 1) :
    (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool,
        PEqualNP.MetaComplexity.circuitFun (N + N) C z =
          decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
            z (Fin.natAdd N l) = true)) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 (N + N) D ∧
        (∀ y : Fin (N + N) → Bool,
          PEqualNP.MetaComplexity.circuitFun (N + N) D y =
            decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧
              y (Fin.natAdd N l) = true)) ∧
        D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 1) := by
  intro q N I _ C _ _ _ unique ao correct
  let E := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
  have mem (p l : Fin N) : (p,l) ∈ E ↔ I p l := by simp [E]
  have noFour : ∀ (p p' : Fin N) (l k : Fin N), p ≠ p' → l ≠ k →
      ¬((p,l) ∈ E ∧ (p,k) ∈ E ∧ (p',l) ∈ E ∧ (p',k) ∈ E) := by
    intro p p' l k hpp hlk hrect
    obtain ⟨l0, hl0, huniq⟩ := unique p p' hpp
    have hll : l = l0 := huniq l
      ⟨(mem p l).mp hrect.1, (mem p' l).mp hrect.2.2.1⟩
    have hkl : k = l0 := huniq k
      ⟨(mem p k).mp hrect.2.1, (mem p' k).mp hrect.2.2.2⟩
    exact hlk (hll.trans hkl.symm)
  have agrees (z : Fin (N + N) → Bool) :
      PEqualNP.MetaComplexity.circuitFun (N + N) C z =
        decide (∃ p l, (p,l) ∈ E ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true) := by
    simpa only [mem] using correct z
  obtain ⟨A, B, cover, budget⟩ := hbudget N N E C noFour ao agrees
  obtain ⟨D, dao, dsize, deval, dread⟩ := hstar N N E A B cover
  exact ⟨D, dao, fun y => by simpa only [mem] using deval y,
    dsize.trans budget, dread⟩
