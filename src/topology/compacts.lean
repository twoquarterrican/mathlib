/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
import data.set_like.basic
import topology.homeomorph

/-!
# Compact sets

We define a few type of sets in a topological space.

## Main Definitions

For a topological space `α`,
- `closeds α`: The type of closed sets.
- `compacts α`: The type of compact sets.
- `nonempty_compacts α`: The type of non-empty compact sets.
- `positive_compacts α`: The type of compact sets with non-empty interior.
-/

open set

variables {α β : Type*} [topological_space α] [topological_space β]

namespace topological_space

/-! ### Closed sets -/

/-- The type of closed subsets of a topological space. -/
structure closeds (α : Type*) [topological_space α] :=
(carrier : set α)
(closed' : is_closed carrier)

namespace closeds
variables {α}

instance : set_like (closeds α) α :=
{ coe := closeds.carrier,
  coe_injective' := λ s t h, by { cases s, cases t, congr' } }

lemma closed (s : closeds α) : is_closed (s : set α) := s.closed'

@[ext] protected lemma ext {s t : closeds α} (h : s.1 = t.1) : s = t := set_like.ext' h

@[simp] lemma coe_mk (s : set α) (h) : (mk s h : set α) = s := rfl

instance : has_sup (closeds α) := ⟨λ s t, ⟨s ∪ t, s.closed.union t.closed⟩⟩
instance : has_inf (closeds α) := ⟨λ s t, ⟨s ∩ t, s.closed.inter t.closed⟩⟩
instance : has_top (closeds α) := ⟨⟨univ, is_closed_univ⟩⟩
instance : has_bot (closeds α) := ⟨⟨∅, is_closed_empty⟩⟩

instance : lattice (closeds α) := set_like.coe_injective.lattice _ (λ _ _, rfl) (λ _ _, rfl)
instance : bounded_order (closeds α) := bounded_order.lift (coe : _ → set α) (λ _ _, id) rfl rfl

/-- The type of closed sets is inhabited, with default element the empty set. -/
instance : inhabited (closeds α) := ⟨⊥⟩

@[simp] lemma coe_sup (s t : closeds α) : (↑(s ⊔ t) : set α) = s ∪ t := rfl
@[simp] lemma coe_inf (s t : closeds α) : (↑(s ⊓ t) : set α) = s ∩ t := rfl
@[simp] lemma coe_top : (↑(⊤ : closeds α) : set α) = univ := rfl
@[simp] lemma coe_bot : (↑(⊥ : closeds α) : set α) = ∅ := rfl

end closeds

/-! ### Compact sets -/

/-- The type of compact sets of a topological space. -/
structure compacts (α : Type*) [topological_space α] :=
(carrier : set α)
(compact' : is_compact carrier)

namespace compacts

instance : set_like (compacts α) α :=
{ coe := compacts.carrier,
  coe_injective' := λ s t h, by { cases s, cases t, congr' } }

lemma compact (s : compacts α) : is_compact (s : set α) := s.compact'

@[ext] protected lemma ext {s t : compacts α} (h : (s : set α) = t) : s = t := set_like.ext' h

@[simp] lemma coe_mk (s : set α) (h) : (mk s h : set α) = s := rfl

instance : has_sup (compacts α) := ⟨λ s t, ⟨s ∪ t, s.compact.union t.compact⟩⟩
instance [t2_space α] : has_inf (compacts α) := ⟨λ s t, ⟨s ∩ t, s.compact.inter t.compact⟩⟩
instance [compact_space α] : has_top (compacts α) := ⟨⟨univ, compact_univ⟩⟩
instance : has_bot (compacts α) := ⟨⟨∅, is_compact_empty⟩⟩

instance : semilattice_sup (compacts α) := set_like.coe_injective.semilattice_sup _ (λ _ _, rfl)

instance [t2_space α] : lattice (compacts α) :=
set_like.coe_injective.lattice _ (λ _ _, rfl) (λ _ _, rfl)

instance : order_bot (compacts α) := order_bot.lift (coe : _ → set α) (λ _ _, id) rfl

instance [compact_space α] : bounded_order (compacts α) :=
bounded_order.lift (coe : _ → set α) (λ _ _, id) rfl rfl

/-- The type of compact sets is inhabited, with default element the empty set. -/
instance : inhabited (compacts α) := ⟨⊥⟩

@[simp] lemma coe_sup (s t : compacts α) : (↑(s ⊔ t) : set α) = s ∪ t := rfl
@[simp] lemma coe_inf [t2_space α] (s t : compacts α) : (↑(s ⊓ t) : set α) = s ∩ t := rfl
@[simp] lemma coe_top [compact_space α] : (↑(⊤ : compacts α) : set α) = univ := rfl
@[simp] lemma coe_bot : (↑(⊥ : compacts α) : set α) = ∅ := rfl

@[simp] lemma coe_finset_sup {ι : Type*} {s : finset ι} {f : ι → compacts α} :
  (↑(s.sup f) : set α) = s.sup (λ i, f i) :=
begin
  classical,
  refine finset.induction_on s rfl (λ a s _ h, _),
  simp_rw [finset.sup_insert, coe_sup, sup_eq_union],
  congr',
end

/-- The image of a compact set under a continuous function. -/
protected def map (f : α → β) (hf : continuous f) (K : compacts α) : compacts β :=
⟨f '' K.1, K.2.image hf⟩

@[simp] lemma coe_map {f : α → β} (hf : continuous f) (s : compacts α) :
  (s.map f hf : set β) = f '' s := rfl

/-- A homeomorphism induces an equivalence on compact sets, by taking the image. -/
@[simp] protected def equiv (f : α ≃ₜ β) : compacts α ≃ compacts β :=
{ to_fun := compacts.map f f.continuous,
  inv_fun := compacts.map _ f.symm.continuous,
  left_inv := λ s, by { ext1, simp only [coe_map, ← image_comp, f.symm_comp_self, image_id] },
  right_inv := λ s, by { ext1, simp only [coe_map, ← image_comp, f.self_comp_symm, image_id] } }

/-- The image of a compact set under a homeomorphism can also be expressed as a preimage. -/
lemma equiv_to_fun_val (f : α ≃ₜ β) (K : compacts α) :
  (compacts.equiv f K).1 = f.symm ⁻¹' K.1 :=
congr_fun (image_eq_preimage_of_inverse f.left_inv f.right_inv) K.1

end compacts

/-! ### Nonempty compact sets -/

/-- The type of nonempty compact sets of a topological space. -/
structure nonempty_compacts (α : Type*) [topological_space α] extends compacts α :=
(nonempty' : carrier.nonempty)

namespace nonempty_compacts

instance : set_like (nonempty_compacts α) α :=
{ coe := λ s, s.carrier,
  coe_injective' := λ s t h, by { obtain ⟨⟨_, _⟩, _⟩ := s, obtain ⟨⟨_, _⟩, _⟩ := t, congr' } }

lemma compact (s : nonempty_compacts α) : is_compact (s : set α) := s.compact'
protected lemma nonempty (s : nonempty_compacts α) : (s : set α).nonempty := s.nonempty'

/-- Reinterpret a nonempty compact as a closed set. -/
def to_closeds [t2_space α] (s : nonempty_compacts α) : closeds α := ⟨s, s.compact.is_closed⟩

@[ext] protected lemma ext {s t : nonempty_compacts α} (h : (s : set α) = t) : s = t :=
set_like.ext' h

@[simp] lemma coe_mk (s : compacts α) (h) : (mk s h : set α) = s := rfl

instance : has_sup (nonempty_compacts α) :=
⟨λ s t, ⟨s.to_compacts ⊔ t.to_compacts, s.nonempty.mono $ subset_union_left _ _⟩⟩
instance [compact_space α] [nonempty α] : has_top (nonempty_compacts α) := ⟨⟨⊤, univ_nonempty⟩⟩

instance : semilattice_sup (nonempty_compacts α) :=
set_like.coe_injective.semilattice_sup _ (λ _ _, rfl)

instance [compact_space α] [nonempty α] : order_top (nonempty_compacts α) :=
order_top.lift (coe : _ → set α) (λ _ _, id) rfl

@[simp] lemma coe_sup (s t : nonempty_compacts α) : (↑(s ⊔ t) : set α) = s ∪ t := rfl
@[simp] lemma coe_top [compact_space α] [nonempty α] :
  (↑(⊤ : nonempty_compacts α) : set α) = univ := rfl

/-- In an inhabited space, the type of nonempty compact subsets is also inhabited, with
default element the singleton set containing the default element. -/
instance [inhabited α] : inhabited (nonempty_compacts α) :=
⟨{ carrier := {default}, compact' := is_compact_singleton, nonempty' := singleton_nonempty _ }⟩

instance to_compact_space {s : nonempty_compacts α} : compact_space s :=
⟨is_compact_iff_is_compact_univ.1 s.compact⟩

instance to_nonempty {s : nonempty_compacts α} : nonempty s := s.nonempty.to_subtype

end nonempty_compacts

/-! ### Positive compact sets -/

/-- The type of compact sets nonempty interior of a topological space. See also `compacts` and
`nonempty_compacts` -/
structure positive_compacts (α : Type*) [topological_space α] extends compacts α :=
(interior_nonempty' : (interior carrier).nonempty)

namespace positive_compacts

instance : set_like (positive_compacts α) α :=
{ coe := λ s, s.carrier,
  coe_injective' := λ s t h, by { obtain ⟨⟨_, _⟩, _⟩ := s, obtain ⟨⟨_, _⟩, _⟩ := t, congr' } }

lemma compact (s : positive_compacts α) : is_compact (s : set α) := s.compact'
lemma interior_nonempty (s : positive_compacts α) : (interior (s : set α)).nonempty :=
s.interior_nonempty'

/-- Reinterpret a positive compact as a nonempty compact. -/
def to_nonempty_compacts (s : positive_compacts α) : nonempty_compacts α :=
⟨s.to_compacts, s.interior_nonempty.mono interior_subset⟩

@[ext] protected lemma ext {s t : positive_compacts α} (h : (s : set α) = t) : s = t :=
set_like.ext' h

@[simp] lemma coe_mk (s : compacts α) (h) : (mk s h : set α) = s := rfl

instance : has_sup (positive_compacts α) :=
⟨λ s t, ⟨s.to_compacts ⊔ t.to_compacts,
  s.interior_nonempty.mono $ interior_mono $ subset_union_left _ _⟩⟩
instance [compact_space α] [nonempty α] : has_top (positive_compacts α) :=
⟨⟨⊤, interior_univ.symm.subst univ_nonempty⟩⟩

instance : semilattice_sup (positive_compacts α) :=
set_like.coe_injective.semilattice_sup _ (λ _ _, rfl)

instance [compact_space α] [nonempty α] : order_top (positive_compacts α) :=
order_top.lift (coe : _ → set α) (λ _ _, id) rfl

@[simp] lemma coe_sup (s t : positive_compacts α) : (↑(s ⊔ t) : set α) = s ∪ t := rfl
@[simp] lemma coe_top [compact_space α] [nonempty α] :
  (↑(⊤ : positive_compacts α) : set α) = univ := rfl

instance [compact_space α] [nonempty α] : inhabited (positive_compacts α) := ⟨⊤⟩

/-- In a nonempty locally compact space, there exists a compact set with nonempty interior. -/
instance [locally_compact_space α] [nonempty α] : nonempty (positive_compacts α) :=
let ⟨s, hs⟩ := exists_compact_subset is_open_univ $ mem_univ (classical.arbitrary α) in
  ⟨{ carrier := s, compact' := hs.1, interior_nonempty' := ⟨_, hs.2.1⟩ }⟩

end positive_compacts
end topological_space
