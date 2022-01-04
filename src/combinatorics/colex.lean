/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov
-/
import data.fintype.basic
import algebra.geom_sum

/-!
# Colex

We define the colex ordering for finite sets, and give a couple of important
lemmas and properties relating to it.

The colex ordering likes to avoid large values - it can be thought of on
`finset ℕ` as the "binary" ordering. That is, order s based on
`∑_{i ∈ s} 2^i`.
It's defined here in a slightly more general way, requiring only `has_lt α` in
the definition of colex on `finset α`. In the context of the Kruskal-Katona
theorem, we are interested in particular on how colex behaves for sets of a
fixed size. If the size is 3, colex on ℕ starts
123, 124, 134, 234, 125, 135, 235, 145, 245, 345, ...

## Main statements
* `colex.hom_lt_iff`: strictly monotone functions preserve colex
* Colex order properties - linearity, decidability and so on.
* `forall_lt_of_colex_lt_of_forall_lt`: if s < t in colex, and everything
  in t is < t, then everything in s is < t. This confirms the idea that
  an enumeration under colex will exhaust all sets using elements < t before
  allowing t to be included.
* `sum_two_pow_le_iff_lt`: colex for α = ℕ is the same as binary
  (this also proves binary expansions are unique)

## See also

Related files are:
* `data.list.lex`: Lexicographic order on lists.
* `data.psigma.order`: Lexicographic order on `Σ' i, α i`.
* `data.sigma.order`: Lexicographic order on `Σ i, α i`.
* `order.lexicographic`: Lexicographic order on `α × β`.

## Tags
colex, colexicographic, binary

## References
* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf
-/

open_locale big_operators

variable {α : Type*}

open finset

/-- If everything in `s` is less than `k`, we can bound the sum of powers. -/
lemma nat.sum_two_pow_lt {k : ℕ} {s : finset ℕ} (h : ∀ ⦃x⦄, x ∈ s → x < k) :
  s.sum (pow 2) < 2^k :=
begin
  refine (sum_le_sum_of_subset $ λ t ht, mem_range.2 $ h ht).trans_lt _,
  have h' := geom_sum_mul_add 1 k,
  rw [geom_sum, mul_one, one_add_one_eq_two] at h',
  rw ←h',
  exact nat.lt_succ_self _,
end

namespace finset

/--
We define this type synonym to refer to the colexicographic ordering on finsets
rather than the natural subset ordering.
-/
@[derive inhabited]
def colex (α) := finset α

/-- `to_colex` is the identity function from `finset α` to `colex α`. -/
def to_colex : finset α ≃ colex α := ⟨id, id, λ h, rfl, λ h, rfl⟩

/-- `of_colex` is the identity function from `colex α` to `finset α`. -/
def of_colex : colex α ≃ finset α := ⟨id, id, λ h, rfl, λ h, rfl⟩

@[simp] lemma to_colex_symm_eq : (@to_colex α).symm = of_colex := rfl
@[simp] lemma of_colex_symm_eq : (@of_colex α).symm = to_colex := rfl
@[simp] lemma to_colex_of_colex (s : colex α) : to_colex (of_colex s) = s := rfl
@[simp] lemma of_colex_to_colex (s : finset α) : of_colex (to_colex s) = s := rfl
@[simp] lemma to_colex_inj {s t : finset α} : to_colex s = to_colex t ↔ s = t := iff.rfl
@[simp] lemma of_colex_inj {s t : colex α} : of_colex s = of_colex t ↔ s = t := iff.rfl

namespace colex

instance [has_lt α] : has_le (colex α) :=
⟨λ s t, ∀ a, (∀ ⦃b⦄, a < b → (b ∈ s.of_colex ↔ b ∈ t.of_colex)) → a ∈ s.of_colex → a ∈ t.of_colex⟩

/--
`s` is less than `t` in the colex ordering if the largest thing that's not in both sets is in t.
In other words, max (s Δ t) ∈ t (if the maximum exists).
-/
instance [has_lt α] : has_lt (colex α) :=
⟨λ s t, ∃ a, (∀ ⦃b⦄, a < b → (b ∈ s.of_colex ↔ b ∈ t.of_colex)) ∧ a ∉ s.of_colex ∧ a ∈ t.of_colex⟩

lemma le_def [has_lt α] (s t : colex α) :
  s ≤ t ↔
    ∀ a, (∀ ⦃b⦄, a < b → (b ∈ s.of_colex ↔ b ∈ t.of_colex)) → a ∈ s.of_colex → a ∈ t.of_colex :=
iff.rfl

lemma lt_def [has_lt α] (s t : finset α) :
  s.to_colex < t.to_colex ↔ ∃ k, (∀ {x}, k < x → (x ∈ s ↔ x ∈ t)) ∧ k ∉ s ∧ k ∈ t :=
iff.rfl

instance [preorder α] : preorder (colex α) :=
{ le_refl := λ s _ _, id,
  le_trans := λ s t u hst htu a h ha, begin
    refine htu _ _ (hst _ _ ha),

  end,
  lt_iff_le_not_le := λ s t,
  begin
    split,
    { intro t,
      refine ⟨or.inl t, _⟩,
      rintro (i | rfl),
      { apply asymm_of _ t i },
      { apply irrefl _ t } },
    rintro ⟨h₁ | rfl, h₂⟩,
    { apply h₁ },
    apply h₂.elim (or.inr rfl),
  end,
  ..colex.has_lt, ..colex.has_le }

/-- Strictly monotone functions preserve the colex ordering. -/
lemma hom_lt_iff {β : Type*} [linear_order α] [decidable_eq β] [preorder β]
  {f : α → β} (h₁ : strict_mono f) (s t : finset α) :
  (s.image f).to_colex < (t.image f).to_colex ↔ s.to_colex < t.to_colex :=
begin
  simp only [colex.lt_def, not_exists, mem_image, exists_prop, not_and],
  split,
  { rintro ⟨k, z, q, k', _, rfl⟩,
    exact ⟨k', λ x hx, by simpa [h₁.injective.eq_iff] using z (h₁ hx), λ t, q _ t rfl, ‹k' ∈ t›⟩ },
  rintro ⟨k, z, ka, _⟩,
  refine ⟨f k, λ x hx, _, _, k, ‹k ∈ t›, rfl⟩,
  { split,
    any_goals
    { rintro ⟨x', hx', rfl⟩,
      refine ⟨x', _, rfl⟩,
      rwa ← z _ <|> rwa z _,
      rwa strict_mono.lt_iff_lt h₁ at hx } },
  { simp only [h₁.injective, function.injective.eq_iff],
    exact λ x hx, ne_of_mem_of_not_mem hx ka }
end

/-- s special case of `colex.hom_lt_iff` which is sometimes useful. -/
@[simp] lemma hom_fin_lt_iff {n : ℕ} (s t : finset (fin n)) :
  (s.image (λ i : fin n, (i : ℕ))).to_colex < (t.image (λ i : fin n, (i : ℕ))).to_colex
   ↔ s.to_colex < t.to_colex :=
colex.hom_lt_iff (λ x y k, k) _ _

instance [has_lt α] : is_irrefl (colex α) (<) :=
⟨λ s h, exists.elim h (λ _ ⟨_,a,b⟩, a b)⟩

@[trans]
lemma lt_trans [linear_order α] {a b c : colex α} :
  a < b → b < c → a < c :=
begin
  rintros ⟨k₁, k₁z, notinA, inB⟩ ⟨k₂, k₂z, notinB, inC⟩,
  cases lt_or_gt_of_ne (ne_of_mem_of_not_mem inB notinB),
  { refine ⟨k₂, _, by rwa k₁z h, inC⟩,
    intros x hx,
    rw ← k₂z hx,
    apply k₁z (trans h hx) },
  { refine ⟨k₁, _, notinA, by rwa ← k₂z h⟩,
    intros x hx,
    rw k₁z hx,
    apply k₂z (trans h hx) }
end

@[trans]
lemma le_trans [linear_order α] (a b c : colex α) :
  a ≤ b → b ≤ c → a ≤ c :=
λ AB BC, AB.elim (λ k, BC.elim (λ t, or.inl (lt_trans k t)) (λ t, t ▸ AB)) (λ k, k.symm ▸ BC)

instance [linear_order α] : is_trans (colex α) (<) := ⟨λ _ _ _, colex.lt_trans⟩

lemma lt_trichotomy [linear_order α] (s t : colex α) :
  s < t ∨ s = t ∨ t < s :=
begin
  by_cases h₁ : (s = t),
  { tauto },
  rcases (exists_max_image (s \ t ∪ t \ s) id _) with ⟨k, hk, z⟩,
  { simp only [mem_union, mem_sdiff] at hk,
    cases hk,
    { right,
      right,
      refine ⟨k, λ t th, _, hk.2, hk.1⟩,
      specialize z t,
      by_contra h₂,
      simp only [mem_union, mem_sdiff, id.def] at z,
      rw [not_iff, iff_iff_and_or_not_and_not, not_not, and_comm] at h₂,
      apply not_le_of_lt th (z h₂) },
    { left,
      refine ⟨k, λ t th, _, hk.2, hk.1⟩,
      specialize z t,
      by_contra h₃,
      simp only [mem_union, mem_sdiff, id.def] at z,
      rw [not_iff, iff_iff_and_or_not_and_not, not_not, and_comm, or_comm] at h₃,
      apply not_le_of_lt th (z h₃) }, },
  rw nonempty_iff_ne_empty,
  intro a,
  simp only [union_eq_empty_iff, sdiff_eq_empty_iff_subset] at a,
  apply h₁ (subset.antisymm a.1 a.2)
end

instance [linear_order α] : is_trichotomous (colex α) (<) := ⟨lt_trichotomy⟩

instance decidable_lt [linear_order α] : ∀ {s t : colex α}, decidable (s < t) :=
λ s t, decidable_of_iff'
  (∃ (k ∈ t.of_colex), (∀ x ∈ s.of_colex ∪ t.of_colex, k < x → (x ∈ s.of_colex ↔ x ∈ t.of_colex)) ∧ k ∉ s.of_colex)
  begin
    rw colex.lt_def,
    apply exists_congr,
    simp only [mem_union, exists_prop, or_imp_distrib, and_comm (_ ∈ t), and_assoc],
    intro k,
    refine and_congr_left' (forall_congr _),
    tauto,
  end

instance [linear_order α] : linear_order (colex α) :=
{ le_refl := λ s, or.inr rfl,
  le_trans := le_trans,
  le_antisymm := λ s t AB BA, AB.elim (λ k, BA.elim (λ t, (asymm k t).elim) (λ t, t.symm)) id,
  le_total := λ s t,
          (lt_trichotomy s t).elim3 (or.inl ∘ or.inl) (or.inl ∘ or.inr) (or.inr ∘ or.inl),
  decidable_le := λ s t, by apply_instance,
  decidable_lt := λ s t, by apply_instance,
  decidable_eq := λ s t, by apply_instance,
  lt_iff_le_not_le := λ s t,
  begin
    split,
    { intro t,
      refine ⟨or.inl t, _⟩,
      rintro (i | rfl),
      { apply asymm_of _ t i },
      { apply irrefl _ t } },
    rintro ⟨h₁ | rfl, h₂⟩,
    { apply h₁ },
    apply h₂.elim (or.inr rfl),
  end,
  ..colex.has_lt,
  ..colex.has_le }

/-- The instances set up let us infer that `colex.lt` is a strict total order. -/
example [linear_order α] : is_strict_total_order (colex α) (<) := infer_instance

/-- Strictly monotone functions preserve the colex ordering. -/
lemma hom_le_iff {β : Type*} [linear_order α] [linear_order β]
  {f : α → β} (h₁ : strict_mono f) (s t : finset α) :
  (s.image f).to_colex ≤ (t.image f).to_colex ↔ s.to_colex ≤ t.to_colex :=
by rw [le_iff_le_iff_lt_iff_lt, hom_lt_iff h₁]

/-- s special case of `colex_hom` which is sometimes useful. -/
@[simp] lemma hom_fin_le_iff {n : ℕ} (s t : finset (fin n)) :
  (s.image (λ i : fin n, (i : ℕ))).to_colex ≤ (t.image (λ i : fin n, (i : ℕ))).to_colex
   ↔ s.to_colex ≤ t.to_colex :=
colex.hom_le_iff (λ x y k, k) _ _

/--
If `s` is before `t` in colex, and everything in `t` is small, then everything in `s` is small.
-/
lemma forall_lt_of_colex_lt_of_forall_lt [linear_order α] {s t : finset α}
  (t : α) (h₁ : s.to_colex < t.to_colex) (h₂ : ∀ x ∈ t, x < t) :
  ∀ x ∈ s, x < t :=
begin
  rw colex.lt_def at h₁,
  rcases h₁ with ⟨k, z, _, _⟩,
  intros x hx,
  apply lt_of_not_ge,
  intro a,
  refine not_lt_of_ge a (h₂ x _),
  rwa ← z,
  apply lt_of_lt_of_le (h₂ k ‹_›) a,
end

/-- `s.to_colex < {r}.to_colex` iff all elements of `s` are less than `r`. -/
lemma lt_singleton_iff_mem_lt [linear_order α] {r : α} {s : finset α} :
  s.to_colex < ({r} : finset α).to_colex ↔ ∀ x ∈ s, x < r :=
begin
  simp only [lt_def, mem_singleton, ←and_assoc, exists_eq_right],
  split,
  { intros t x hx,
    rw ←not_le,
    intro h,
    rcases lt_or_eq_of_le h with h₁ | rfl,
    { exact ne_of_irrefl h₁ ((t.1 h₁).1 hx).symm },
    { exact t.2 hx } },
  { exact λ h, ⟨λ z hz, ⟨λ i, (asymm hz (h _ i)).elim, λ i, (hz.ne' i).elim⟩, by simpa using h r⟩ }
end

/-- If {r} is less than or equal to s in the colexicographical sense,
  then s contains an element greater than or equal to r. -/
lemma mem_le_of_singleton_le [linear_order α] {r : α} {s : finset α}:
  ({r} : finset α).to_colex ≤ s.to_colex ↔ ∃ x ∈ s, r ≤ x :=
by { rw ←not_lt, simp [lt_singleton_iff_mem_lt] }

/-- Colex is an extension of the base ordering on α. -/
lemma singleton_lt_iff_lt [linear_order α] {r s : α} :
  ({r} : finset α).to_colex < ({s} : finset α).to_colex ↔ r < s :=
by simp [lt_singleton_iff_mem_lt]

/-- Colex is an extension of the base ordering on α. -/
lemma singleton_le_iff_le [linear_order α] {r s : α} :
  ({r} : finset α).to_colex ≤ ({s} : finset α).to_colex ↔ r ≤ s :=
by rw [le_iff_le_iff_lt_iff_lt, singleton_lt_iff_lt]

/-- Colex doesn't care if you remove the other set -/
@[simp] lemma sdiff_lt_sdiff_iff_lt [has_lt α] [decidable_eq α] (s t : finset α) :
  (s \ t).to_colex < (t \ s).to_colex ↔ s.to_colex < t.to_colex :=
begin
  rw [colex.lt_def, colex.lt_def],
  apply exists_congr,
  intro k,
  simp only [mem_sdiff, not_and, not_not],
  split,
  { rintro ⟨z, kAB, kB, kA⟩,
    refine ⟨_, kA, kB⟩,
    { intros x hx,
      specialize z hx,
      tauto } },
  { rintro ⟨z, kA, kB⟩,
    refine ⟨_, λ _, kB, kB, kA⟩,
    intros x hx,
    rw z hx },
end

/-- Colex doesn't care if you remove the other set -/
@[simp] lemma sdiff_le_sdiff_iff_le [linear_order α] (s t : finset α) :
  (s \ t).to_colex ≤ (t \ s).to_colex ↔ s.to_colex ≤ t.to_colex :=
by rw [le_iff_le_iff_lt_iff_lt, sdiff_lt_sdiff_iff_lt]

lemma empty_to_colex_lt [linear_order α] {s : finset α} (hA : s.nonempty) :
  (∅ : finset α).to_colex < s.to_colex :=
begin
  rw [colex.lt_def],
  refine ⟨max' _ hA, _, by simp, max'_mem _ _⟩,
  simp only [false_iff, not_mem_empty],
  intros x hx t,
  apply not_le_of_lt hx (le_max' _ _ t),
end

/-- If `s ⊂ t`, then `s` is less than `t` in the colex order. Note the converse does not hold, as
`⊆` is not a linear order. -/
lemma colex_lt_of_ssubset [linear_order α] {s t : finset α} (h : s ⊂ t) :
  s.to_colex < t.to_colex :=
begin
  rw [←sdiff_lt_sdiff_iff_lt, sdiff_eq_empty_iff_subset.2 h.1],
  exact empty_to_colex_lt (by simpa [finset.nonempty] using exists_of_ssubset h),
end

@[simp] lemma empty_to_colex_le [linear_order α] {s : finset α} :
  (∅ : finset α).to_colex ≤ s.to_colex :=
begin
  rcases s.eq_empty_or_nonempty with rfl | hA,
  { simp },
  { apply (empty_to_colex_lt hA).le },
end

/-- If `s ⊆ t`, then `s ≤ t` in the colex order. Note the converse does not hold, as `⊆` is not a
linear order. -/
lemma colex_le_of_subset [linear_order α] {s t : finset α} (h : s ⊆ t) :
  s.to_colex ≤ t.to_colex :=
begin
  rw [←sdiff_le_sdiff_iff_le, sdiff_eq_empty_iff_subset.2 h],
  apply empty_to_colex_le
end

/-- The function from finsets to finsets with the colex order is a relation homomorphism. -/
@[simps]
def to_colex_rel_hom [linear_order α] :
  ((⊆) : finset α → finset α → Prop) →r ((≤) : colex α → colex α → Prop) :=
{ to_fun := finset.to_colex,
  map_rel' := λ s t, colex_le_of_subset }

instance [linear_order α] : order_bot (colex α) :=
{ bot := (∅ : finset α).to_colex,
  bot_le := λ x, empty_to_colex_le }

instance [linear_order α] [fintype α] : order_top (colex α) :=
{ top := finset.univ.to_colex,
  le_top := λ x, colex_le_of_subset (subset_univ _) }

instance [linear_order α] : lattice (colex α) :=
{ ..(by apply_instance : semilattice_sup (colex α)),
  ..(by apply_instance : semilattice_inf (colex α)) }

instance [linear_order α] [fintype α] : bounded_order (colex α) :=
{ ..(by apply_instance : order_top (colex α)),
  ..(by apply_instance : order_bot (colex α)) }

/-- For subsets of ℕ, we can show that colex is equivalent to binary. -/
lemma sum_two_pow_lt_iff_lt (s t : finset ℕ) :
  ∑ i in s, 2^i < ∑ i in t, 2^i ↔ s.to_colex < t.to_colex :=
begin
  have z : ∀ (s t : finset ℕ), s.to_colex < t.to_colex → ∑ i in s, 2^i < ∑ i in t, 2^i,
  { intros s t,
    rw [← sdiff_lt_sdiff_iff_lt, colex.lt_def],
    rintro ⟨k, z, kA, kB⟩,
    rw ← sdiff_union_inter s t,
    conv_rhs { rw ← sdiff_union_inter t s },
    rw [sum_union (disjoint_sdiff_inter _ _), sum_union (disjoint_sdiff_inter _ _),
        inter_comm, add_lt_add_iff_right],
    apply lt_of_lt_of_le (@nat.sum_two_pow_lt k (s \ t) _),
    { apply single_le_sum (λ _ _, nat.zero_le _) kB },
    intros x hx,
    apply lt_of_le_of_ne (le_of_not_lt (λ kx, _)),
    { apply (ne_of_mem_of_not_mem hx kA) },
    have := (z kx).1 hx,
    rw mem_sdiff at this hx,
    exact hx.2 this.1 },
  refine ⟨λ h, (lt_trichotomy s t).resolve_right (λ h₁, h₁.elim _ (not_lt_of_gt h ∘ z _ _)), z s t⟩,
  rintro rfl,
  apply irrefl _ h
end

/-- For subsets of ℕ, we can show that colex is equivalent to binary. -/
lemma sum_two_pow_le_iff_lt (s t : finset ℕ) :
  ∑ i in s, 2^i ≤ ∑ i in t, 2^i ↔ s.to_colex ≤ t.to_colex :=
by rw [le_iff_le_iff_lt_iff_lt, sum_two_pow_lt_iff_lt]

end colex
end finset
