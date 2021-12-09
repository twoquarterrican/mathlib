/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaël Dillies
-/
import combinatorics.set_family.compression.uv
import data.finset.lattice

/-!
# Shadows

This file defines shadows of a set family. The shadow of a set family is the set family of sets we
get by removing any element from any set of the original family. If one pictures `finset α` as a big
hypercube (each dimension being membership of a given element), then taking the shadow corresponds
to projecting each finset down once in all available directions.

## Main definitions

The `shadow` of a set family is everything we can get by removing an element from each set.

## Notation

`∂ 𝒜` is notation for `shadow 𝒜`. It is situated in locale `finset_family`.

We also maintain the convention that `a, b : α` are elements of the ground type, `s, t : finset α`
are finsets, and `𝒜, ℬ : finset (finset α)` are finset families.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf
* http://discretemath.imp.fu-berlin.de/DMII-2015-16/kruskal.pdf

## Tags

shadow, set family
-/

open finset nat uv
open_locale finset_family

variables {α : Type*}

namespace finset
variables [decidable_eq α] {𝒜 : finset (finset α)} {s t : finset α} {a : α} {k : ℕ}

/-- The shadow of a set family `𝒜` is all sets we can get by removing one element from any set in
`𝒜`, and the (`k` times) iterated shadow (`shadow^[k]`) is all sets we can get by removing `k`
elements from any set in `𝒜`. -/
def shadow (𝒜 : finset (finset α)) : finset (finset α) := 𝒜.sup (λ s, s.image (erase s))

localized "notation `∂ `:90 := finset.shadow" in finset_family

/-- The shadow of the empty set is empty. -/
@[simp] lemma shadow_empty : ∂ (∅ : finset (finset α)) = ∅ := rfl

/-- The shadow is monotone. -/
@[mono] lemma shadow_monotone : monotone (shadow : finset (finset α) → finset (finset α)) :=
λ 𝒜 ℬ, sup_mono

/-- `s` is in the shadow of `𝒜` iff there is an `t ∈ 𝒜` from which we can remove one element to
get `s`. -/
lemma mem_shadow_iff : s ∈ ∂ 𝒜 ↔ ∃ t ∈ 𝒜, ∃ a ∈ t, erase t a = s :=
by simp only [shadow, mem_sup, mem_image]

lemma erase_mem_shadow (hs : s ∈ 𝒜) (ha : a ∈ s) : erase s a ∈ ∂ 𝒜 :=
mem_shadow_iff.2 ⟨s, hs, a, ha, rfl⟩

/-- `t` is in the shadow of `𝒜` iff we can add an element to it so that the resulting finset is in
`𝒜`. -/
lemma mem_shadow_iff_insert_mem : s ∈ ∂ 𝒜 ↔ ∃ a ∉ s, insert a s ∈ 𝒜 :=
begin
  refine mem_shadow_iff.trans ⟨_, _⟩,
  { rintro ⟨s, hs, a, ha, rfl⟩,
    refine ⟨a, not_mem_erase a s, _⟩,
    rwa insert_erase ha },
  { rintro ⟨a, ha, hs⟩,
    exact ⟨insert a s, hs, a, mem_insert_self _ _, erase_insert ha⟩ }
end

/-- `s ∈ ∂ 𝒜` iff `s` is exactly one element less than something from `𝒜` -/
lemma mem_shadow_iff_exists_mem_card_add_one :
  s ∈ ∂ 𝒜 ↔ ∃ t ∈ 𝒜, s ⊆ t ∧ t.card = s.card + 1 :=
begin
  refine mem_shadow_iff_insert_mem.trans ⟨_, _⟩,
  { rintro ⟨a, ha, hs⟩,
    exact ⟨insert a s, hs, subset_insert _ _, card_insert_of_not_mem ha⟩ },
  { rintro ⟨t, ht, hst, h⟩,
    obtain ⟨a, ha⟩ : ∃ a, t \ s = {a} :=
      card_eq_one.1 (by rw [card_sdiff hst, h, add_tsub_cancel_left]),
    exact ⟨a, λ hat,
      not_mem_sdiff_of_mem_right hat ((ha.ge : _ ⊆ _) $ mem_singleton_self a),
      by rwa [insert_eq a s, ←ha, sdiff_union_of_subset hst]⟩ }
end

/-- Being in the shadow of `𝒜` means we have a superset in `𝒜`. -/
lemma exists_subset_of_mem_shadow (hs : s ∈ ∂ 𝒜) : ∃ t ∈ 𝒜, s ⊆ t :=
let ⟨t, ht, hst⟩ := mem_shadow_iff_exists_mem_card_add_one.1 hs in ⟨t, ht, hst.1⟩

/-- `t ∈ ∂^k 𝒜` iff `t` is exactly `k` elements less than something in `𝒜`. -/
lemma mem_shadow_iff_exists_mem_card_add :
  s ∈ (∂^[k]) 𝒜 ↔ ∃ t ∈ 𝒜, s ⊆ t ∧ t.card = s.card + k :=
begin
  induction k with k ih generalizing 𝒜 s,
  { refine ⟨λ hs, ⟨s, hs, subset.refl _, rfl⟩, _⟩,
    rintro ⟨t, ht, hst, hcard⟩,
    rwa eq_of_subset_of_card_le hst hcard.le },
  simp only [exists_prop, function.comp_app, function.iterate_succ],
  refine ih.trans _,
  clear ih,
  split,
  { rintro ⟨t, ht, hst, hcardst⟩,
    obtain ⟨u, hu, htu, hcardtu⟩ := mem_shadow_iff_exists_mem_card_add_one.1 ht,
    refine ⟨u, hu, hst.trans htu, _⟩,
    rw [hcardtu, hcardst],
    refl },
  { rintro ⟨t, ht, hst, hcard⟩,
    obtain ⟨u, hsu, hut, hu⟩ := finset.exists_intermediate_set k
      (by { rw [add_comm, hcard], exact le_succ _ }) hst,
    rw add_comm at hu,
    refine ⟨u, mem_shadow_iff_exists_mem_card_add_one.2 ⟨t, ht, hut, _⟩, hsu, hu⟩,
    rw [hcard, hu],
    refl }
end

lemma sdiff_sdiff {A B C : finset α} (h : C ⊆ A) : A \ (B \ C) = A \ B ∪ C :=
begin
  ext1 i,
  simp only [mem_union, not_and, mem_sdiff],
  push_neg,
  refine ⟨_, _⟩,
  rintro ⟨iA, iBC⟩,
  by_cases (i ∈ C),
  right, exact h,
  left,
  refine ⟨iA, mt iBC h⟩,
  rintro (⟨iA, niB⟩ | iC),
  refine ⟨iA, λ iB, (niB iB).elim⟩,
  refine ⟨h iC, λ _, iC⟩,
end

/-- Here's the key fact about compression for Kruskal-Katona. If, for all `x ∈ U` there is
`y ∈ V` such that `𝒜` is `(U-x,V-y)`-compressed, then UV-compression will reduce the size of the
shadow of `𝒜`. -/
lemma card_shadow_compression_le {U V : finset α} (hvu : V = ∅ → U = ∅)
  (h₁ : ∀ x ∈ U, ∃ y ∈ V, is_compressed (erase U x) (erase V y) 𝒜) :
  (∂ (𝓒 U V 𝒜)).card ≤ (∂ 𝒜).card :=
begin
  set 𝒜' := 𝓒 U V 𝒜,
  suffices : (∂ 𝒜' \ ∂ 𝒜).card ≤ (∂ 𝒜 \ ∂ 𝒜').card,
  { suffices z : (∂ 𝒜' \ ∂ 𝒜 ∪ ∂ 𝒜' ∩ ∂ 𝒜).card ≤ (∂ 𝒜 \ ∂ 𝒜' ∪ ∂ 𝒜 ∩ ∂ 𝒜').card,
    { rwa [sdiff_union_inter, sdiff_union_inter] at z },
    rw [card_disjoint_union, card_disjoint_union, inter_comm],
    apply add_le_add_right ‹_›,
    any_goals { apply disjoint_sdiff_inter } },

  -- We'll define an injection ∂ 𝒜' \ ∂ 𝒜 → ∂ 𝒜 \ ∂ 𝒜'. First, let's prove
  -- a few facts about things in the domain:
  suffices q₁ : ∀ B ∈ ∂ 𝒜' \ ∂ 𝒜, U ⊆ B ∧ disjoint V B ∧ (B ∪ V) \ U ∈ ∂ 𝒜 \ ∂ 𝒜',
  { apply card_le_card_of_inj_on (λ B, (B ∪ V) \ U) (λ B HB, (q₁ B HB).2.2),
    intros B₁ HB₁ B₂ HB₂ k,
    exact sup_sdiff_inj_on _ _ ⟨(q₁ B₁ HB₁).2.1, (q₁ B₁ HB₁).1⟩ ⟨(q₁ B₂ HB₂).2.1, (q₁ B₂ HB₂).1⟩ k },
  intros B HB,
  obtain ⟨k, k'⟩: B ∈ ∂ 𝒜' ∧ B ∉ ∂ 𝒜 := mem_sdiff.1 HB,
  -- This is gonna be useful a couple of times so let's name it.
  have m: ∀ y ∉ B, insert y B ∉ 𝒜 := λ y H a, k' (mem_shadow_iff_insert_mem.2 ⟨y, H, a⟩),
  rcases mem_shadow_iff_insert_mem.1 k with ⟨x, _, _⟩,
  have q := compress_moved ‹insert x B ∈ 𝒜'› (m _ ‹x ∉ B›),
  have : disjoint V B := (disjoint_insert_right.1 q.2.1).2,
  have dVU : disjoint V U := disjoint_of_subset_right q.1 q.2.1,
  have : V \ U = V := sdiff_eq_self_of_disjoint ‹disjoint V U›,
  -- The first key part is that x ∉ U
  have : x ∉ U,
  { intro a,
    rcases h₁ x ‹x ∈ U› with ⟨y, Hy, xy_comp⟩,
    -- If `x ∈ U`, we can get `y ∈ V` so that `𝒜` is `(U-x,V-y)`-compressed
    apply m y (disjoint_left.1 ‹disjoint V B› Hy),
    -- and we'll use this `y` to contradict `m`.
    rw is_compressed at xy_comp,
    have : (insert x B ∪ V) \ U ∈ 𝓒 (erase U x) (erase V y) 𝒜,
      rw xy_comp, exact q.2.2,
    -- So we'd like to show insert y B ∈ 𝒜.
    -- We do this by showing the below
    have : ((insert x B ∪ V) \ U ∪ erase U x) \ erase V y ∈ 𝒜,
      apply sup_sdiff_mem_of_mem_compression this _,
        apply disjoint_of_subset_left (erase_subset _ _) disjoint_sdiff,
      rw [union_sdiff_distrib, ‹V \ U = V›],
      apply subset.trans (erase_subset _ _) (subset_union_right _ _),
    -- and then arguing that it's the same
    suffices : ((insert x B ∪ V) \ U ∪ erase U x) \ erase V y = insert y B,
      rwa ← this,
    have : x ∉ B ∪ V := not_mem_union.2 ⟨‹x ∉ B›, disjoint_right.1 ‹disjoint V U› a⟩,
    have : erase U x ⊆ insert x B ∪ V := trans (erase_subset x _)
                                          (trans q.1 (subset_union_left _ V)),
    -- which is just a pain.
    rw [← sdiff_sdiff ‹U.erase x ⊆ insert x B ∪ V›, finset.sdiff_erase ‹x ∈ U›,
        sdiff_singleton_eq_erase, insert_union, erase_insert ‹x ∉ B ∪ V›, union_sdiff_distrib,
        sdiff_erase ‹y ∈ V›, sdiff_eq_self_of_disjoint, union_comm, insert_eq],
    rw [disjoint.comm],
    apply disjoint_of_subset_left (erase_subset _ _) ‹disjoint V B› },
  -- Now that that's done, it's immediate that U ⊆ B
  have : U ⊆ B, rw [← erase_eq_of_not_mem ‹x ∉ U›, ← subset_insert_iff], exact q.1,
  -- and we already had that V and B are disjoint
  refine ⟨‹_›, ‹_›, _⟩,
  -- so it only remains to get (B ∪ V) \ U ∈ ∂ 𝒜 \ ∂ 𝒜'
  rw mem_sdiff,
  have : x ∉ V := disjoint_right.1 q.2.1 (mem_insert_self _ _),
  split,
    -- (B ∪ V) \ U ∈ ∂ 𝒜 is pretty direct:
  { rw mem_shadow_iff_insert_mem,
    refine ⟨x, _, _⟩,
    { simp [mem_sdiff, mem_union], tauto! },
    convert q.2.2,
    rw [insert_eq, insert_eq, union_assoc, union_sdiff_distrib _ (B ∪ V),
        sdiff_eq_self_of_disjoint (disjoint_singleton_left.2 ‹x ∉ U›)] },
  -- For (B ∪ V) \ U ∉ ∂ 𝒜', we split up based on w ∈ U
  rw mem_shadow_iff_insert_mem,
  rintro ⟨w, hwB, hw𝒜'⟩,
  by_cases (w ∈ U),
    -- If w ∈ U, we find z ∈ V, and contradict m again
  { rcases h₁ w ‹w ∈ U› with ⟨z, Hz, xy_comp⟩,
    apply m z (disjoint_left.1 ‹disjoint V B› Hz),
    have : insert w ((B ∪ V) \ U) ∈ 𝒜,
    { refine mem_of_mem_compression hw𝒜' (subset.trans _ (subset_insert _ _)) hvu,
      rw union_sdiff_distrib, rw ‹V \ U = V›, apply subset_union_right },
    have : (insert w ((B ∪ V) \ U) ∪ erase U w) \ erase V z ∈ 𝒜,
    { refine sup_sdiff_mem_of_mem_compression _ _ _,
          rw is_compressed at xy_comp, rwa xy_comp,
        apply subset.trans (erase_subset _ _),
        apply subset.trans _ (subset_insert _ _),
        rw [union_sdiff_distrib, ‹V \ U = V›], apply subset_union_right,
      rw disjoint_insert_right, split, apply not_mem_erase,
      apply disjoint_of_subset_left (erase_subset _ _), apply disjoint_sdiff },
    have : (insert w ((B ∪ V) \ U) ∪ erase U w) \ erase V z = insert z B,
    { rw [insert_union, ← union_insert, insert_erase h,
        sdiff_union_of_subset (subset.trans ‹U ⊆ B› (subset_union_left _ _)),
        union_sdiff_distrib, sdiff_eq_self_of_disjoint
        (disjoint_of_subset_right (erase_subset _ _) ‹disjoint V B›.symm),
        ← sdiff_singleton_eq_erase, sdiff_sdiff_self_left,
        inter_singleton_of_mem Hz, union_comm],
      refl },
    rwa ← this },
  -- If w ∉ U, we contradict m again
  rw [mem_sdiff, ← not_imp, not_not] at hwB,
  have : w ∉ V := h ∘ hwB ∘ mem_union_right _,
  have : w ∉ B := h ∘ hwB ∘ mem_union_left _,
  apply m w this,

  have : (insert w ((B ∪ V) \ U) ∪ U) \ V ∈ 𝒜,
    refine sup_sdiff_mem_of_mem_compression ‹insert w ((B ∪ V) \ U) ∈ 𝒜'›
            (trans _ (subset_insert _ _)) _,
      rw [union_sdiff_distrib, ‹V \ U = V›], apply subset_union_right,
      rw disjoint_insert_right, exact ⟨‹_›, disjoint_sdiff⟩,
  convert this, rw [insert_union, sdiff_union_of_subset (trans ‹U ⊆ B› (subset_union_left _ _)),
                    ← insert_union, union_sdiff_self], symmetry,
  rw [_root_.sdiff_eq_self_iff_disjoint],
  exact disjoint_insert_right.2 ⟨‹w ∉ V›, ‹disjoint V B›⟩,
end

end finset
