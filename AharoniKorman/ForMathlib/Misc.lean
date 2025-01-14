/-
Copyright (c) 2024 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import Mathlib.Order.Chain
import Mathlib.Order.WellFoundedSet

/-!
# Results for mathlib

A collection of results for the disproof of the Aharoni–Korman conjecture which should be in
mathlib.
-/

/--
If the image of `s` under `f` is finite, and each fiber of `f` has a finite intersection
with `s`, then `s` is itself finite.
-/
lemma Set.Finite.of_finite_fibers {α β : Type*} (f : α → β) {s : Set α}
    (himage : (f '' s).Finite)
    (hfibers : ∀ x ∈ f '' s, (s ∩ f ⁻¹' {x}).Finite) : s.Finite :=
  (himage.biUnion hfibers).subset <| fun x ↦ by aesop

/--
If `α` is a linear order with well-founded `<`, then the universe is a partially well-ordered set.
Note this does not hold without the linearity assumption.
-/
lemma univ_isPWO_of_linearOrder {α : Type*} [LinearOrder α] [WellFoundedLT α] :
    (Set.univ : Set α).IsPWO := by
  rw [← Set.isWF_iff_isPWO, Set.isWF_univ_iff]
  exact wellFounded_lt

open Finset

lemma Finset.surjOn_of_injOn_of_card_le {α β : Type*} {s : Finset α} {t : Finset β}
    (f : α → β) (hf : Set.MapsTo f s t) (hinj : Set.InjOn f s) (hst : #t ≤ #s) :
    Set.SurjOn f s t := by
  classical
  suffices s.image f = t by simp [← this, Set.SurjOn]
  have : s.image f ⊆ t := by aesop (add simp Finset.subset_iff)
  exact eq_of_subset_of_card_le this (hst.trans_eq (card_image_of_injOn hinj).symm)

lemma Finset.surj_on_of_inj_on_of_card_le_again {α β : Type*} {s : Finset α} {t : Finset β}
    (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
    (hinj : ∀ a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂) (hst : #t ≤ #s) :
    ∀ b ∈ t, ∃ a ha, b = f a ha := by
  let f' : s → β := fun a ↦ f a a.property
  have hinj' : Set.InjOn f' s.attach := fun x hx y hy hxy => Subtype.ext (hinj _ _ x.2 y.2 hxy)
  have hmapsto' : Set.MapsTo f' s.attach t := fun x hx => hf _ _
  intro b hb
  obtain ⟨a, ha, rfl⟩ := surjOn_of_injOn_of_card_le f' hmapsto' hinj' (by rwa [card_attach]) hb
  exact ⟨a, a.2, rfl⟩

lemma Finset.injOn_of_surjOn_of_card_le {α β : Type*} {s : Finset α} {t : Finset β}
    (f : α → β) (hf : Set.MapsTo f s t) (hsurj : Set.SurjOn f s t) (hst : #s ≤ #t) :
    Set.InjOn f s := by
  classical
  rw [← card_image_iff]
  have : s.image f = t := Finset.coe_injective <| by simp [hsurj.image_eq_of_mapsTo hf]
  have : #(s.image f) = #t := by rw [this]
  have : #(s.image f) ≤ #s := card_image_le
  omega

lemma chain_intersect_antichain {α : Type*} [PartialOrder α] {s t : Set α}
    (hs : IsChain (· ≤ ·) s) (ht : IsAntichain (· ≤ ·) t) :
    (s ∩ t).Subsingleton := by
  simp only [Set.Subsingleton, Set.mem_inter_iff, and_imp]
  intro x hxs hxt y hys hyt
  by_contra! hne
  cases hs.total hxs hys
  case inl h => exact ht hxt hyt hne h
  case inr h => exact ht hyt hxt hne.symm h

lemma IsChain.le_of_not_lt {α : Type*} [Preorder α] {s : Set α} (hs : IsChain (· ≤ ·) s)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) (h : ¬ x < y) : y ≤ x := by
  cases hs.total hx hy with
  | inr h' => exact h'
  | inl h' => simpa [lt_iff_le_not_le, h'] using h

lemma IsChain.lt_of_not_le {α : Type*} [Preorder α] {s : Set α} (hs : IsChain (· ≤ ·) s)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) (h : ¬ x ≤ y) : y < x :=
  (hs.total hx hy).elim (h · |>.elim) (lt_of_le_not_le · h)

lemma Set.SurjOn.of_comp {α β γ : Type*}
    {r : Set α} {s : Set β} {t : Set γ} {f : α → β} {g : β → γ}
    (h : Set.SurjOn (g ∘ f) r t) (hr : Set.MapsTo f r s) : Set.SurjOn g s t := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := h hz
  exact ⟨f x, hr hx, rfl⟩

lemma isChain_union {α : Type*} [Preorder α] {s t : Set α} :
    IsChain (· ≤ ·) (s ∪ t) ↔
      IsChain (· ≤ ·) s ∧ IsChain (· ≤ ·) t ∧ ∀ a ∈ s, ∀ b ∈ t, a ≠ b → a ≤ b ∨ b ≤ a := by
  rw [IsChain, IsChain, IsChain, Set.pairwise_union_of_symmetric]
  intro x y
  exact Or.symm

variable {α β : Type*}

section sectL

variable [Preorder α] [PartialOrder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
  [DecidableRel (α := α × β) (· ≤ ·)] (a b : α) (c : β)

lemma Prod.Icc_map_sectL : (Icc a b).map (.sectL _ c) = Icc (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm, not_lt_of_le, le_of_lt])

lemma Prod.Ioc_map_sectL : (Ioc a b).map (.sectL _ c) = Ioc (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm, not_lt_of_le, le_of_lt])

lemma Prod.Ico_map_sectL : (Ico a b).map (.sectL _ c) = Ico (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm, not_lt_of_le, le_of_lt])

lemma Prod.Ioo_map_sectL : (Ioo a b).map (.sectL _ c) = Ioo (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm, not_lt_of_le, le_of_lt])

end sectL

section sectR

variable [PartialOrder α] [Preorder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
  [DecidableRel (α := α × β) (· ≤ ·)] (c : α) (a b : β)

lemma Prod.Icc_map_sectR : (Icc a b).map (.sectR c _) = Icc (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm, not_lt_of_le, le_of_lt])

lemma Prod.Ioc_map_sectR : (Ioc a b).map (.sectR c _) = Ioc (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm, not_lt_of_le, le_of_lt])

lemma Prod.Ico_map_sectR : (Ico a b).map (.sectR c _) = Ico (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm, not_lt_of_le, le_of_lt])

lemma Prod.Ioo_map_sectR : (Ioo a b).map (.sectR c _) = Ioo (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm, not_lt_of_le, le_of_lt])

end sectR
