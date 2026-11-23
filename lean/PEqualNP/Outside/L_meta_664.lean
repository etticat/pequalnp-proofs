import Mathlib

namespace PEqualNP.Outside.L_meta_664

namespace AffineQuad664
variable {F : Type} [Field F] [CharP F 2]

def q (b : F) (p : F × F) := p.1^2 + b*p.1*p.2 + p.2^2

def cross (b : F) (p d : F × F) := b*(p.1*d.2+p.2*d.1)

def H (a c : F) : F →+ F where
  toFun t := a*t^2+c*t
  map_zero' := by simp
  map_add' := by intro x y; rw [CharTwo.add_sq]; ring

theorem q_line (b : F) (p d : F × F) (t : F) :
    q b (p + t • d) = q b p + H (q b d) (cross b p d) t := by
  change (p.1 + t*d.1)^2 + b*(p.1+t*d.1)*(p.2+t*d.2) + (p.2+t*d.2)^2 =
    q b p + (q b d*t^2 + cross b p d*t)
  rw [CharTwo.add_sq,CharTwo.add_sq]
  unfold q cross
  ring

theorem eq_zero_of_q (b : F) (noRoot : ∀ X : F, X^2+b*X+1 ≠ 0)
    (p : F × F) (h : q b p = 0) : p = 0 := by
  obtain ⟨x,y⟩ := p
  change x^2 + b*x*y + y^2 = 0 at h
  by_cases hy : y = 0
  · subst y
    simp at h
    simp [h]
  · exfalso
    apply noRoot (x/y)
    field_simp
    linear_combination h

theorem bijective_zero [Fintype F] (a : F) (ha : a ≠ 0) : Function.Bijective (H a 0) := by
  apply Finite.injective_iff_bijective.mp
  intro x y h
  change a*x^2+0*x = a*y^2+0*y at h
  simp only [zero_mul,add_zero,mul_right_inj' ha] at h
  apply CharTwo.mul_self_injective
  simpa only [sq] using h

theorem kernel_two (a c : F) (ha : a ≠ 0) (hc : c ≠ 0) : Nat.card (H a c).ker = 2 := by
  have mem (t : F) : H a c t = 0 ↔ t = 0 ∨ t = c/a := by
    change a*t^2 + c*t = 0 ↔ _
    rw [show a*t^2+c*t=t*(a*t+c) by ring,mul_eq_zero,CharTwo.add_eq_zero]
    rw [eq_div_iff ha,mul_comm t a]
  have eq : ((H a c).ker : Set F) = {0, c/a} := by
    ext t
    exact (mem t).trans (by simp)
  change (((H a c).ker : Set F)).ncard = 2
  rw [eq,Set.ncard_pair (Ne.symm (div_ne_zero hc ha))]

theorem offset_outside (b : F) (noRoot : ∀ X : F, X^2+b*X+1 ≠ 0)
    (p d : F × F) (hc : cross b p d ≠ 0) :
    q b p ∉ (H (q b d) (cross b p d)).range := by
  rintro ⟨t,ht⟩
  have z := eq_zero_of_q b noRoot (p+t•d) (by rw [q_line,ht,CharTwo.add_self_eq_zero])
  have zx : p.1 + t*d.1 = 0 := congrArg Prod.fst z
  have zy : p.2 + t*d.2 = 0 := congrArg Prod.snd z
  apply hc
  unfold cross
  rw [CharTwo.add_eq_zero.mp zx,CharTwo.add_eq_zero.mp zy]
  rw [show t*d.2*d.1 = t*d.1*d.2 by ring,CharTwo.add_self_eq_zero,mul_zero]

end AffineQuad664

namespace Counts664

variable {G : Type*} [AddCommGroup G] [Fintype G]

private theorem count_surj_quot (L : G →+ G) (q : G) (A : AddSubgroup G)
    [DecidablePred (· ∈ A)] (hs : Function.Surjective ((QuotientAddGroup.mk' A).comp L)) :
    (Finset.univ.filter (fun t : G => q + L t ∈ A)).card = Nat.card A := by
  classical
  let K := (QuotientAddGroup.mk' A).comp L
  obtain ⟨t₀, ht₀⟩ := hs (-QuotientAddGroup.mk' A q)
  have h₀ : q + L t₀ ∈ A := by
    apply (QuotientAddGroup.eq_zero_iff _).mp
    change QuotientAddGroup.mk' A (q + L t₀) = 0
    rw [map_add]
    change _ + ((QuotientAddGroup.mk' A).comp L) t₀ = 0
    rw [ht₀, add_neg_cancel]
  have hK (t : G) : t ∈ K.ker ↔ L t ∈ A := QuotientAddGroup.eq_zero_iff _
  let E : {t : G // q + L t ∈ A} ≃ K.ker :=
    { toFun := fun t => ⟨t.val - t₀, (hK _).mpr (by
        rw [map_sub, ← add_sub_add_left_eq_sub (L t.val) (L t₀) q]
        exact A.sub_mem t.property h₀)⟩
      invFun := fun s => ⟨s.val + t₀, by
        rw [map_add, show q + (L s.val + L t₀) = L s.val + (q + L t₀) by abel]
        exact A.add_mem ((hK _).mp s.property) h₀⟩
      left_inv := by intro t; ext; simp
      right_inv := by intro s; ext; simp }
  have hcard : Nat.card K.ker = Nat.card A := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := G ⧸ A))
    exact (AddSubgroup.card_ker_mul_card_of_surjective hs).trans A.card_mul_index.symm
  calc
    _ = Nat.card {t : G // q + L t ∈ A} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = Nat.card K.ker := Nat.card_congr E
    _ = Nat.card A := hcard

/-- A bijective additive map meets every translate of a subgroup in its cardinality. -/
theorem count_bijective (L : G →+ G) (q : G) (A : AddSubgroup G)
    [DecidablePred (· ∈ A)] (hbij : Function.Bijective L) :
    (Finset.univ.filter (fun t : G => q + L t ∈ A)).card = Nat.card A :=
  count_surj_quot L q A ((QuotientAddGroup.mk'_surjective A).comp hbij.2)

/-- A coset outside an index-two image either misses the subgroup or contributes its cardinality
when the endomorphism has two-element kernel. -/
theorem count_index_two (L : G →+ G) (q : G) (A : AddSubgroup G)
    [DecidablePred (· ∈ A)] (hker : Nat.card L.ker = 2) (hout : q ∉ L.range) :
    (Finset.univ.filter (fun t : G => q + L t ∈ A)).card = 0 ∨
    (Finset.univ.filter (fun t : G => q + L t ∈ A)).card = Nat.card A := by
  classical
  by_cases hit : ∃ t : G, q + L t ∈ A
  · right
    obtain ⟨t₀, ht₀⟩ := hit
    have hi : L.range.index = 2 := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := L.range))
      rw [← hker]
      exact L.range.index_mul_card.trans (AddSubgroup.card_ker_mul_card_range L).symm
    have hnot : q + L t₀ ∉ L.range := fun h =>
      hout ((L.range.add_mem_cancel_right (show L t₀ ∈ L.range from ⟨t₀, rfl⟩)).mp h)
    apply count_surj_quot L q A
    intro y
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective A y
    by_cases hx : x ∈ L.range
    · obtain ⟨s, rfl⟩ := hx
      exact ⟨s, rfl⟩
    · have hneg : -(q + L t₀) ∉ L.range := fun h => hnot (L.range.neg_mem_iff.mp h)
      have hd : x - (q + L t₀) ∈ L.range := by
        rw [sub_eq_add_neg, L.range.add_mem_iff_of_index_two hi]
        exact ⟨fun h => (hx h).elim, fun h => (hneg h).elim⟩
      obtain ⟨s, hs⟩ := hd
      refine ⟨s, ?_⟩
      change QuotientAddGroup.mk' A (L s) = QuotientAddGroup.mk' A x
      rw [hs, map_sub]
      have hzero : QuotientAddGroup.mk' A (q + L t₀) = 0 :=
        (QuotientAddGroup.eq_zero_iff _).mpr ht₀
      rw [hzero, sub_zero]
  · left
    apply Finset.card_eq_zero.mpr
    exact Finset.filter_false_of_mem (fun t _ ht => hit ⟨t, ht⟩)

end Counts664

namespace AffineQuad664

theorem line_count : ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (b : F), (∀ X : F, X ^ 2 + b * X + 1 ≠ 0) → ∀ (A : AddSubgroup F) [DecidablePred (· ∈ A)] (p d : F × F), d ≠ 0 → ((Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = 0 ∨ (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) ∧ (p = 0 → (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) := by
  intro F _ _ _ _ b noRoot A _ p d hd
  change (((Finset.univ.filter (fun t : F => q b (p + t • d) ∈ A)).card = 0 ∨
    (Finset.univ.filter (fun t : F => q b (p + t • d) ∈ A)).card = Nat.card A) ∧
    (p = 0 → (Finset.univ.filter (fun t : F => q b (p + t • d) ∈ A)).card = Nat.card A))
  simp only [q_line]
  have ha : q b d ≠ 0 := fun h => hd (eq_zero_of_q b noRoot d h)
  by_cases hz : cross b p d = 0
  · rw [hz]
    have count := Counts664.count_bijective (H (q b d) 0) (q b p) A (bijective_zero _ ha)
    exact ⟨Or.inr count,fun _ => count⟩
  · refine ⟨Counts664.count_index_two (H (q b d) (cross b p d)) (q b p) A
        (kernel_two _ _ ha hz) (offset_outside b noRoot p d hz),?_⟩
    rintro rfl
    exact False.elim (hz (by simp [cross]))

end AffineQuad664

end PEqualNP.Outside.L_meta_664

theorem PEqualNP.Outside.L_meta_664 : ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (b : F), (∀ X : F, X ^ 2 + b * X + 1 ≠ 0) → ∀ (A : AddSubgroup F) [DecidablePred (· ∈ A)] (p d : F × F), d ≠ 0 → ((Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = 0 ∨ (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) ∧ (p = 0 → (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) := PEqualNP.Outside.L_meta_664.AffineQuad664.line_count
