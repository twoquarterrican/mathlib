/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes

Adjoining roots of polynomials
-/
import data.polynomial.field_division
import ring_theory.adjoin
import ring_theory.principal_ideal_domain
import linear_algebra.finite_dimensional

/-!
# Adjoining roots of polynomials

This file defines the commutative ring `adjoin_root f`, the ring R[X]/(f) obtained from a
commutative ring `R` and a polynomial `f : R[X]`. If furthermore `R` is a field and `f` is
irreducible, the field structure on `adjoin_root f` is constructed.

## Main definitions and results

The main definitions are in the `adjoin_root` namespace.

*  `mk f : polynomial R →+* adjoin_root f`, the natural ring homomorphism.

*  `of f : R →+* adjoin_root f`, the natural ring homomorphism.

* `root f : adjoin_root f`, the image of X in R[X]/(f).

* `lift (i : R →+* S) (x : S) (h : f.eval₂ i x = 0) : (adjoin_root f) →+* S`, the ring
  homomorphism from R[X]/(f) to S extending `i : R →+* S` and sending `X` to `x`.

-/
noncomputable theory
open_locale classical
open_locale big_operators

universes u v w

variables {R : Type u} {S : Type v} {K : Type w}

open polynomial ideal

/-- Adjoin a root of a polynomial `f` to a commutative ring `R`. We define the new ring
as the quotient of `R` by the principal ideal of `f`. -/
def adjoin_root [comm_ring R] (f : polynomial R) : Type u :=
ideal.quotient (span {f} : ideal (polynomial R))

namespace adjoin_root

section comm_ring
variables [comm_ring R] (f : polynomial R)

instance : comm_ring (adjoin_root f) := ideal.quotient.comm_ring _

instance : inhabited (adjoin_root f) := ⟨0⟩

instance : decidable_eq (adjoin_root f) := classical.dec_eq _

/-- Ring homomorphism from `R[x]` to `adjoin_root f` sending `X` to the `root`. -/
def mk : polynomial R →+* adjoin_root f := ideal.quotient.mk _

@[elab_as_eliminator]
theorem induction_on {C : adjoin_root f → Prop} (x : adjoin_root f)
  (ih : ∀ p : polynomial R, C (mk f p)) : C x :=
quotient.induction_on' x ih

/-- Embedding of the original ring `R` into `adjoin_root f`. -/
def of : R →+* adjoin_root f := (mk f).comp (ring_hom.of C)

instance : algebra R (adjoin_root f) := (of f).to_algebra

@[simp] lemma algebra_map_eq : algebra_map R (adjoin_root f) = of f := rfl

/-- The adjoined root. -/
def root : adjoin_root f := mk f X

variables {f}

instance adjoin_root.has_coe_t : has_coe_t R (adjoin_root f) := ⟨of f⟩

@[simp] lemma mk_self : mk f f = 0 :=
quotient.sound' (mem_span_singleton.2 $ by simp)

@[simp] lemma mk_C (x : R) : mk f (C x) = x := rfl

@[simp] lemma mk_X : mk f X = root f := rfl

@[simp] lemma aeval_eq (p : polynomial R) : aeval (root f) p = mk f p :=
polynomial.induction_on p (λ x, by { rw aeval_C, refl })
  (λ p q ihp ihq, by rw [alg_hom.map_add, ring_hom.map_add, ihp, ihq])
  (λ n x ih, by { rw [alg_hom.map_mul, aeval_C, alg_hom.map_pow, aeval_X,
    ring_hom.map_mul, mk_C, ring_hom.map_pow, mk_X], refl })

theorem adjoin_root_eq_top : algebra.adjoin R ({root f} : set (adjoin_root f)) = ⊤ :=
algebra.eq_top_iff.2 $ λ x, induction_on f x $ λ p,
(algebra.adjoin_singleton_eq_range R (root f)).symm ▸ ⟨p, set.mem_univ _, aeval_eq p⟩

@[simp] lemma eval₂_root (f : polynomial R) : f.eval₂ (of f) (root f) = 0 :=
by rw [← algebra_map_eq, ← aeval_def, aeval_eq, mk_self]

lemma is_root_root (f : polynomial R) : is_root (f.map (of f)) (root f) :=
by rw [is_root, eval_map, eval₂_root]

variables [comm_ring S]

/-- Lift a ring homomorphism `i : R →+* S` to `adjoin_root f →+* S`. -/
def lift (i : R →+* S) (x : S) (h : f.eval₂ i x = 0) : (adjoin_root f) →+* S :=
begin
  apply ideal.quotient.lift _ (eval₂_ring_hom i x),
  intros g H,
  rcases mem_span_singleton.1 H with ⟨y, hy⟩,
  rw [hy, ring_hom.map_mul, coe_eval₂_ring_hom, h, zero_mul]
end

variables {i : R →+* S} {a : S} {h : f.eval₂ i a = 0}

@[simp] lemma lift_mk {g : polynomial R} : lift i a h (mk f g) = g.eval₂ i a :=
ideal.quotient.lift_mk _ _ _

@[simp] lemma lift_root : lift i a h (root f) = a := by rw [root, lift_mk, eval₂_X]

@[simp] lemma lift_of {x : R} : lift i a h x = i x :=
by rw [← mk_C x, lift_mk, eval₂_C]

@[simp] lemma lift_comp_of : (lift i a h).comp (of f) = i :=
ring_hom.ext $ λ _, @lift_of _ _ _ _ _ _ _ h _

variables (f) [algebra R S]

/-- Produce an algebra homomorphism `adjoin_root f →ₐ[R] S` sending `root f` to
a root of `f` in `S`. -/
def lift_hom (x : S) (hfx : aeval x f = 0) : adjoin_root f →ₐ[R] S :=
{ commutes' := λ r, show lift _ _ hfx r = _, from lift_of, .. lift (algebra_map R S) x hfx }

@[simp] lemma coe_lift_hom (x : S) (hfx : aeval x f = 0) :
  (lift_hom f x hfx : adjoin_root f →+* S) = lift (algebra_map R S) x hfx := rfl

@[simp] lemma aeval_alg_hom_eq_zero (ϕ : adjoin_root f →ₐ[R] S) : aeval (ϕ (root f)) f = 0 :=
begin
  have h : ϕ.to_ring_hom.comp (of f) = algebra_map R S := ring_hom.ext_iff.mpr (ϕ.commutes),
  rw [aeval_def, ←h, ←ring_hom.map_zero ϕ.to_ring_hom, ←eval₂_root f, hom_eval₂],
  refl,
end

@[simp] lemma lift_hom_eq_alg_hom (f : polynomial R) (ϕ : adjoin_root f →ₐ[R] S) :
  lift_hom f (ϕ (root f)) (aeval_alg_hom_eq_zero f ϕ) = ϕ :=
begin
  suffices : ϕ.equalizer (lift_hom f (ϕ (root f)) (aeval_alg_hom_eq_zero f ϕ)) = ⊤,
  { exact (alg_hom.ext (λ x, (subalgebra.ext_iff.mp (this) x).mpr algebra.mem_top)).symm },
  rw [eq_top_iff, ←adjoin_root_eq_top, algebra.adjoin_le_iff, set.singleton_subset_iff],
  exact (@lift_root _ _ _ _ _ _ _ (aeval_alg_hom_eq_zero f ϕ)).symm,
end

/-- If `E` is a field extension of `F` and `f` is a polynomial over `F` then the set
of maps from `F[x]/(f)` into `E` is in bijection with the set of roots of `f` in `E`. -/
def equiv (F E : Type*) [field F] [field E] [algebra F E] (f : polynomial F) (hf : f ≠ 0) :
  (adjoin_root f →ₐ[F] E) ≃ {x // x ∈ (f.map (algebra_map F E)).roots} :=
{ to_fun := λ ϕ, ⟨ϕ (root f), begin
    rw [mem_roots (map_ne_zero hf), is_root.def, ←eval₂_eq_eval_map],
    exact aeval_alg_hom_eq_zero f ϕ,
    exact field.to_nontrivial E, end⟩,
  inv_fun := λ x, lift_hom f ↑x (begin
    rw [aeval_def, eval₂_eq_eval_map, ←is_root.def, ←mem_roots (map_ne_zero hf)],
    exact subtype.mem x,
    exact field.to_nontrivial E end),
  left_inv := λ ϕ, lift_hom_eq_alg_hom f ϕ,
  right_inv := λ x, begin
    ext,
    refine @lift_root F E _ f _ _ ↑x _,
    rw [eval₂_eq_eval_map, ←is_root.def, ←mem_roots (map_ne_zero hf), ←multiset.mem_to_finset],
    exact multiset.mem_to_finset.mpr (subtype.mem x),
    exact field.to_nontrivial E end }

end comm_ring

variables [field K] {f : polynomial K} [irreducible f]

instance is_maximal_span : is_maximal (span {f} : ideal (polynomial K)) :=
principal_ideal_ring.is_maximal_of_irreducible ‹irreducible f›

noncomputable instance field : field (adjoin_root f) :=
ideal.quotient.field (span {f} : ideal (polynomial K))

lemma coe_injective : function.injective (coe : K → adjoin_root f) :=
(of f).injective

variable (f)

lemma mul_div_root_cancel :
  ((X - C (root f)) * (f.map (of f) / (X - C (root f))) : polynomial (adjoin_root f)) =
    f.map (of f) :=
mul_div_eq_iff_is_root.2 $ is_root_root _

section findim
open vector_space
open finite_dimensional

/-- The restriction of `adjoin_root.mk f` to the polynomials of degree less than `f`,
viewed as a isomorphism between vector spaces over `K`. -/
def degree_lt_linear_equiv (hf : f ≠ 0) : degree_lt K (f.nat_degree) ≃ₗ[K] adjoin_root f :=
{ to_fun := λ q, adjoin_root.mk f q,
  inv_fun := λ g, ⟨(classical.some (quotient.mk_surjective g)) % f,
    by { rw [mem_degree_lt, ← degree_eq_nat_degree hf], exact euclidean_domain.mod_lt _ hf }⟩,
  map_add' := λ _ _, ring_hom.map_add _ _ _,
  map_smul' := λ _ _, by { simp only [algebra.smul_def, ring_hom.map_mul, submodule.coe_smul,
    algebra_map_eq, mul_eq_mul_right_iff], left, refl },
  left_inv :=
  begin
    intro p,
    ext1,
    let g := (mk f) p,
    let g' := classical.some (quotient.mk_surjective g),
    have hg' : mk f g' = g := classical.some_spec (quotient.mk_surjective g),
    change g' % f = ↑p,
    have key : ∃ c, g' % f = p + c * f,
    { cases (mem_span_singleton.mp (ideal.quotient.eq.mp hg')) with q hq,
      use q - (g' / f),
      rw [euclidean_domain.mod_eq_sub_mul_div, sub_eq_iff_eq_add.mp hq],
      ring },
    cases key with c key,
    rw key,
    replace key : (↑p + c * f).degree < f.degree,
    { rw ← key, exact euclidean_domain.mod_lt g' hf },
    by_cases c = 0,
    { rw [h, zero_mul, add_zero] },
    { rw [←zero_add f.degree, degree_add_eq_of_degree_lt, degree_mul,
        with_bot.add_lt_add_iff_right (bot_lt_iff_ne_bot.mpr (mt degree_eq_bot.mp hf))] at key,
      { exact false.rec _ (h (degree_eq_bot.mp ((nat.with_bot.lt_zero_iff c.degree).mp key))) },
      { rw [mul_comm, degree_mul, degree_eq_nat_degree hf],
        exact lt_add_of_lt_of_nonneg' (mem_degree_lt.mp (subtype.mem p))
          (le_of_not_lt (mt (nat.with_bot.lt_zero_iff c.degree).mp (mt degree_eq_bot.mp h))) } },
  end,
  right_inv :=
  begin
    intro g,
    let g' := classical.some (quotient.mk_surjective g),
    change (mk f) (g' % f) = g,
    rw ← classical.some_spec (quotient.mk_surjective g),
    exact (ideal.quotient.eq.mpr (mem_span_singleton.mpr
      ⟨g' / f, (eq_sub_iff_add_eq.mpr (euclidean_domain.div_add_mod g' f)).symm⟩)).symm,
  end }

lemma finite_dimensional (hf : f ≠ 0) : finite_dimensional K (adjoin_root f) :=
linear_equiv.finite_dimensional (((polynomial.degree_lt_equiv K (f.nat_degree)).symm).trans
  (degree_lt_linear_equiv f hf))

lemma findim (hf : f ≠ 0) : finite_dimensional.findim K (adjoin_root f) = f.nat_degree :=
by rw [←linear_equiv.findim_eq (((polynomial.degree_lt_equiv K (f.nat_degree)).symm).trans
      (degree_lt_linear_equiv f hf)), finite_dimensional.findim_fintype_fun_eq_card K,
      fintype.card_fin]

end findim
end adjoin_root
