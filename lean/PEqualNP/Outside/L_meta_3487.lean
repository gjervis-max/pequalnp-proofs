import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify

namespace PEqualNP.Outside.L_meta_3487_aux
open Finset

private theorem tangent (d : ℕ) : 174*d ≤ (d*d-d) + 7656 := by
  have hd : d ≤ d*d := by
    cases d with
    | zero => decide
    | succ d => nlinarith
  rcases le_or_gt d 87 with h | h
  · have := Nat.zero_le ((87-d)*(88-d))
    zify [show d ≤ 88 by omega, h] at this
    zify [hd]
    nlinarith only [this]
  · have h' : 88 ≤ d := by omega
    have := Nat.zero_le ((d-87)*(d-88))
    zify [show 87 ≤ d by omega, h'] at this
    zify [hd]
    nlinarith only [this]

theorem side {n : ℕ} (E : Finset (Fin n × Fin n))
    (rect : ∀ a b c d : Fin n, a ≠ b → c ≠ d →
      ¬ ((a,c) ∈ E ∧ (b,c) ∈ E ∧ (a,d) ∈ E ∧ (b,d) ∈ E))
    (hsmall : (E.image Prod.fst).card ≤ 7656) :
    E.card ≤ 44*((E.image Prod.fst).card + (E.image Prod.snd).card - 1) := by
  classical
  let A := E.image Prod.fst
  let B := E.image Prod.snd
  let F := fun y : Fin n => A.filter (fun x => (x,y) ∈ E)
  have count : E.card = ∑ y ∈ B, (F y).card := by
    rw [← Finset.card_sigma]
    apply Finset.card_nbij' (fun p => ⟨p.2,p.1⟩) (fun p => (p.2,p.1))
    · intro p hp
      exact mem_sigma.mpr ⟨mem_image_of_mem _ hp,mem_filter.mpr ⟨mem_image_of_mem _ hp,hp⟩⟩
    · intro p hp
      exact (mem_filter.mp (mem_sigma.mp hp).2).2
    · intro p _; rfl
    · intro p _; rfl
  have pairs : (B.sigma fun y => (F y).offDiag).card ≤ A.offDiag.card := by
    apply card_le_card_of_injOn (fun p => p.2)
    · intro p hp
      obtain ⟨ha,hb,hab⟩ := mem_offDiag.mp (mem_sigma.mp hp).2
      exact mem_offDiag.mpr ⟨(mem_filter.mp ha).1,(mem_filter.mp hb).1,hab⟩
    · rintro ⟨y,a,b⟩ hy ⟨z,c,d⟩ hz h
      change (a,b) = (c,d) at h
      cases h
      obtain ⟨ha,hb,hab⟩ := mem_offDiag.mp (mem_sigma.mp hy).2
      obtain ⟨hc,hd,_⟩ := mem_offDiag.mp (mem_sigma.mp hz).2
      have eq : y = z := by
        by_contra hn
        exact rect a b y z hab hn ⟨(mem_filter.mp ha).2,(mem_filter.mp hb).2,
          (mem_filter.mp hc).2,(mem_filter.mp hd).2⟩
      cases eq
      rfl
  simp only [card_sigma, offDiag_card] at pairs
  have total := Finset.sum_le_sum (s := B) (fun y _ => tangent (F y).card)
  rw [← Finset.mul_sum, ← count, Finset.sum_add_distrib] at total
  simp only [sum_const, nsmul_eq_mul] at total
  change E.card ≤ 44*(A.card+B.card-1)
  by_cases hA : A.card = 0
  · have hE : E = ∅ := by simpa [A] using hA
    simp [hE]
  have pos : A.card ≥ 1 := by omega
  have cap := Nat.mul_le_mul_right (A.card-1) hsmall
  change A.card * (A.card-1) ≤ _ at cap
  rw [Nat.mul_sub, Nat.mul_one] at cap
  have hcombined : 174*E.card ≤ 7656*(A.card-1) + B.card*7656 :=
    total.trans (Nat.add_le_add_right (pairs.trans cap) _)
  rw [show A.card+B.card-1 = (A.card-1)+B.card by omega]
  omega

end PEqualNP.Outside.L_meta_3487_aux

theorem PEqualNP.Outside.L_meta_3487 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)), (∀ (x3 x4 x5 x6 : Fin x1), x3 ≠ x4 → x5 ≠ x6 → ¬((x3, x5) ∈ x2 ∧ (x4, x5) ∈ x2 ∧ (x3, x6) ∈ x2 ∧ (x4, x6) ∈ x2)) → Min.min (Finset.image Prod.fst x2).card (Finset.image Prod.snd x2).card ≤ (7656 : ℕ) → x2.card ≤ (44 : ℕ) * ((Finset.image Prod.fst x2).card + (Finset.image Prod.snd x2).card - (1 : ℕ)) := by
  classical
  intro n E rect h
  rcases min_le_iff.mp h with h | h
  · exact PEqualNP.Outside.L_meta_3487_aux.side E rect h
  let T := E.image Prod.swap
  have memT (a b : Fin n) : (a,b) ∈ T ↔ (b,a) ∈ E := by
    simp [T, Finset.mem_image, Prod.swap_eq_iff_eq_swap]
  have fstT : T.image Prod.fst = E.image Prod.snd := by
    rw [Finset.image_image]; rfl
  have sndT : T.image Prod.snd = E.image Prod.fst := by
    rw [Finset.image_image]; rfl
  have cardT : T.card = E.card := Finset.card_image_of_injective _ Prod.swap_injective
  have res := PEqualNP.Outside.L_meta_3487_aux.side T (by
    intro a b c d hab hcd ⟨hac,hbc,had,hbd⟩
    exact rect c d a b hcd hab ⟨(memT _ _).mp hac,(memT _ _).mp had,
      (memT _ _).mp hbc,(memT _ _).mp hbd⟩) (fstT ▸ h)
  simpa only [cardT, fstT, sndT, Nat.add_comm] using res
