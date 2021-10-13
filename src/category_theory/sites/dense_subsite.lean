/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.sites.sheaf
import category_theory.sites.cover_preserving

/-!
# Dense subsites

We define `cover_dense` functors between sites as functors such that
1. For each object in `D`, there exists a covering sieve in `D` that factors through images of `G`.
2. For each map `f : G(X) ⟶ G(Y)` in `D`, there exists a covering sieve `{ gᵢ }` in `C` such that
   each `G(gᵢ) ≫ f` has a preimage wrt `G`.

## Main results

- `category_theory.factor_cover_sieve_exists`: If `G : C ⥤ D` is cover-preserving and cover-dense,
then given any finite family of morphisms `{ fᵢ : X ⟶ G(Yᵢ) }`, there exists a covering sieve of
`X` that is generated by `{ gⱼ : G(Zⱼ) ⟶ X }` such that each `gⱼ ≫ fᵢ` has a preimage wrt `G`.
- `category_theory.compatible_preserving_of_dense_and_cover_preserving`: If a functor is faithful,
cover-preserving and cover-dense, then it is compatible-preserving.

## References

* [Elephant]: *Sketches of an Elephant*, ℱ. T. Johnstone: C2.2.
* https://ncatlab.org/nlab/show/dense+sub-site
* https://ncatlab.org/nlab/show/comparison+lemma

-/

universes v₁ u₁ u₂

namespace category_theory
section cover_dense
variables {C : Type*} [category C] {D : Type*} [category D] {E : Type*} [category E]
variables (J : grothendieck_topology C) (K : grothendieck_topology D)
variables {L : grothendieck_topology E}

/-- A structure that witnesses the fact that `f` factors through an image object of `G`. -/
@[nolint has_inhabited_instance]
structure factors_through_image_obj (G : C ⥤ D) {V U : D} (f : V ⟶ U) :=
(obj : C) (lift : V ⟶ G.obj obj) (map : G.obj obj ⟶ U) (fac : f = lift ≫ map)

/-- All the arrows in the presieve factors through an image object of `G`. -/
@[nolint has_inhabited_instance]
def all_factors_through_image_obj (G : C ⥤ D) {U : D} (R : presieve U) :=
∀ ⦃V⦄ {f : V ⟶ U} (hf : R f), factors_through_image_obj G f

/--
A structure that witnesses the fact that `f` factors through an image object `G(W)` of `G`,
and that the map `G(W) ≫ fᵢ` has a preimage wrt `G` for each `fᵢ ∈ O`.
-/
@[nolint has_inhabited_instance]
structure factors_through_image_obj_and_map (G : C ⥤ D) {V : D} {U : D} (f : V ⟶ U)
  (O : finset (structured_arrow U G)) extends factors_through_image_obj G f :=
(premap : ∀ (f : O), obj ⟶ f.val.right)
(map_fac : ∀ (f : O), G.map (premap f) = map ≫ f.val.hom)

/--
All the arrows in the presieve factors through an image object of `G`, and the composition of the
factor map with `fᵢ` all has a preimage wrt `G` for each `fᵢ ∈ O`.
-/
@[nolint has_inhabited_instance]
def all_factors_through_image_obj_and_map (G : C ⥤ D) {U : D} (R : presieve U) (O) :=
∀ ⦃V⦄ {f : V ⟶ U} (hf : R f), factors_through_image_obj_and_map G f O

/-- Forgets the additional information about maps. -/
def all_through_both_to_through_obj {G : C ⥤ D} {U} {R : presieve U} {O}
  (H : all_factors_through_image_obj_and_map G R O) : all_factors_through_image_obj G R :=
λ V f hf, (H hf).to_factors_through_image_obj

lemma factors_through_image_obj_and_map.map_fac' {G : C ⥤ D} {V : D} {U : D} {f : V ⟶ U}
  {O : finset (structured_arrow U G)} (H : factors_through_image_obj_and_map G f O) (f' : O) :
  H.lift ≫ G.map (H.premap f') = f ≫ f'.val.hom :=
begin
  rw [H.map_fac f', ← category.assoc],
  congr,
  exact H.fac.symm
end

/--
A helper function that helps constructing a `factors_through_image_obj_and_map` from
`factors_through_image_obj`.
-/
def through_obj_to_through_both {G : C ⥤ D} {U V} {f : V ⟶ U}
  {O : finset (structured_arrow U G)} (H : factors_through_image_obj G f)
  (H' : ∀ (f : O), { g : H.obj ⟶ f.val.right // G.map g = H.map ≫ f.val.hom }) :
  factors_through_image_obj_and_map G f O :=
{ premap := λ f, (H' f).1, map_fac := λ f, (H' f).2, ..H}

/--
A functor `G : (C, J) ⥤ (D, K)` is called `cover_dense` if
1. For each object in `D`, there exists a covering sieve in `D` that factors through images of `G`.
2. For each map `f : G(X) ⟶ G(Y)` in `D`, there exists a covering sieve `{ gᵢ }` in `C` such that
   each `G(gᵢ) ≫ f` has a preimage wrt `G`.

This definition can be found in https://ncatlab.org/nlab/show/dense+sub-site Definition 2.2.
-/
@[nolint has_inhabited_instance]
structure cover_dense (J : grothendieck_topology C) (K : grothendieck_topology D) (G : C ⥤ D) :=
(obj          : ∀ (U : D), K U)
(obj_fac      : ∀ (U : D), all_factors_through_image_obj G (obj U))
(map          : ∀ {U V : C} (f : G.obj U ⟶ G.obj V), J U)
(map_fac_map  : ∀ {U V W} (f : G.obj U ⟶ G.obj V) {g : W ⟶ U} (hg : map f g), W ⟶ V)
(map_fac      : ∀ {U V W} (f : G.obj U ⟶ G.obj V) {g : W ⟶ U} (hg : map f g),
                  G.map (map_fac_map f hg) = G.map g ≫ f)

/-- If `G` is full, then it suffices to provide the covering sieves for the objects. -/
def cover_dense_mk_of_full (J : grothendieck_topology C) (K : grothendieck_topology D) (G : C ⥤ D)
  [full G] (create : ∀ (U : D), Σ (S : K U), all_factors_through_image_obj G S) :
  cover_dense J K G :=
{ obj          := λ U, (create U).1,
  obj_fac      := λ U, (create U).2,
  map          := λ U V f, ⟨_, J.top_mem U⟩,
  map_fac_map  := λ U V W f g hg, g ≫ G.preimage f,
  map_fac      := λ U V W f g hg, by simp }

variables {J} {K} {G : C ⥤ D} (H : cover_dense J K G) (H' : cover_preserving J K G)
variables {X : D} {Y : C} (f : X ⟶ G.obj Y) (S : K X) (HS : all_factors_through_image_obj G S)

/--
Actually the sieve geneated by all the arrows that factors through images of `G` is a covering sieve
of `U : D`/
-/
def cover_dense.obj' (H : cover_dense J K G) (U : D) : K U :=
⟨⟨λ Y f, nonempty (factors_through_image_obj G f), λ Y Z f ⟨hf⟩ g,
  ⟨{ obj := hf.obj, lift := g ≫ hf.lift, map := hf.map, fac := by rw [category.assoc, ←hf.fac] }⟩⟩,
    K.superset_covering (λ V f hf, ⟨H.obj_fac U hf⟩) (H.obj U).property⟩

/-- The witness of `obj'` analogue to `cover_dense.obj_fac`. -/
noncomputable
def cover_dense.obj_fac' (H : cover_dense J K G) (U : D) :
  all_factors_through_image_obj G (H.obj' U) := λ V f hf, hf.some

/-- Every map wose target is in the image of `G` is in `obj'`. -/
lemma cover_dense.obj'_in (H : cover_dense J K G) {U : D} {V : C} (f : G.obj V ⟶ U) :
  H.obj' U f := ⟨{ obj := V, lift := 𝟙 _, map := f, fac := by simp }⟩

include H H' f S HS

/-
In https://ncatlab.org/nlab/show/comparison+lemma, the definition of a dense subsite is given by
1. For each object in `D`, there exists a covering sieve in `D` that factors through images of `G`.
2. For each finite family of morphisms `fᵢ : X ⟶ G(Yᵢ)`, there exists a covering sieve of `X`
   that `all_factors_through_image_obj_and_map` wrt the family.

We will prove that our definition implies 2.
If the topology on `C` is the induced topology, then the converse also holds (not formalized).
-/

/--
Given a covering sieve in `D` that factors through images of `G`, we can construct another
covering sieve that furthermore factors through an image map when composed with `fᵢ`.
-/
@[simps] def factor_cover_sieve_one : K X :=
begin
  split, apply K.bind_covering S.property,
  intros Z g hg,
  exact (K.pullback_stable (HS hg).lift
    (H'.cover_preserve (H.map ((HS hg).map ≫ f)).property) : _)
end

omit f S HS

/-
Thus given any finite family of morphisms `{ fᵢ : X ⟶ G(Yᵢ) }`, we may obtain a covering sieve of
`X` that factors through the image of `G`, and factors through an image map of `G` after composing
with each `fᵢ` by repeated application of `factor_cover_sieve_one`.
-/
lemma factor_cover_sieve_exists (O : finset (structured_arrow X G)) :
  ∃ (S : K X) (H₁ : all_factors_through_image_obj_and_map G S O), true :=
begin
  classical,
  apply finset.induction_on O,
  { use H.obj X, split, swap, trivial,
    intros Y g hg,
    apply through_obj_to_through_both (H.obj_fac X hg),
    intro X, exfalso, exact X.2 },
  rintros f O' - ⟨S, hS, -⟩,
  use factor_cover_sieve_one H H' f.hom S (all_through_both_to_through_obj hS),
  split, swap, trivial,
  intros Y g hg,
  choose Y' g' f' H₁ H₂ H₃ using hg,
  rcases presieve.get_functor_pushforward_structure H₂ with ⟨Y'', g'', f'', H₄, H₅⟩,
  let : factors_through_image_obj G g :=
  { obj := Y'', lift := f'', map := G.map g'' ≫ (hS H₁).map, fac := by
    { rw [← H₃, ← category.assoc, ← H₅, category.assoc], congr, exact (hS H₁).fac } },
  apply through_obj_to_through_both this,
  rintros ⟨f₀, hf₀⟩,
  by_cases hf₀' : f₀ = f,
  { cases hf₀',
    use H.map_fac_map ((hS H₁).map ≫ f.hom) H₄,
    rw category.assoc,
    exact H.map_fac _ H₄ },
  { let hf₀' := finset.mem_of_mem_insert_of_ne hf₀ hf₀',
    use g'' ≫ (hS H₁).premap ⟨f₀, hf₀'⟩,
    rw [G.map_comp, (hS H₁).map_fac ⟨_, hf₀'⟩, category.assoc] }
end

/-- The sieve that `all_factors_through_image_obj_and_map` wrt a `finset`. -/
noncomputable
def factor_cover_sieve {G : C ⥤ D} (H : cover_dense J K G) (H' : cover_preserving J K G)
  {X : D} (O : finset (structured_arrow X G)) : K X :=
(factor_cover_sieve_exists H H' O).some

/-- The witness that `factor_cover_sieve` indeed factors through the image of `G`. -/
noncomputable
def factor_cover_sieve_factor {G : C ⥤ D} (H : cover_dense J K G) (H' : cover_preserving J K G)
  {X : D} (O : finset (structured_arrow X G)) :
  all_factors_through_image_obj_and_map G (factor_cover_sieve H H' O) O :=
(factor_cover_sieve_exists H H' O).some_spec.some

end cover_dense

open presieve opposite structured_arrow
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₁} D]
variables {J : grothendieck_topology C} {K : grothendieck_topology D}
variables {G : C ⥤ D} (H : cover_dense J K G) (H' : cover_preserving J K G)

include H H'

/-
We ought to show that for each `f₁ ≫ G.map g₁ = f₂ ≫ G.map g₂`, the restriction of
`x` along the two paths are the same given `x` is compatible in the image of `G`.
-/
lemma functor_pushforward_compatible_of_dense_subsite
  (ℱ : SheafOfTypes K)
  {Y₁ Y₂ : C} {X Z: D}
  (f₁ : X ⟶ G.obj Y₁) (f₂ : X ⟶ G.obj Y₂) (g₁ : G.obj Y₁ ⟶ Z) (g₂ : G.obj Y₂ ⟶ Z)
  (eq : f₁ ≫ g₁ = f₂ ≫ g₂)
  (x₁ : ℱ.val.obj (op (G.obj Y₁))) (x₂ : ℱ.val.obj (op (G.obj Y₂)))
  (hx : ∀ {X' : C} (f₁' : X' ⟶ Y₁) (f₂' : X' ⟶ Y₂) (h : G.map f₁' ≫ g₁ = G.map f₂' ≫ g₂),
    ℱ.val.map (G.map f₁').op x₁ = ℱ.val.map (G.map f₂').op x₂) :
  ℱ.val.map f₁.op x₁ = ℱ.val.map f₂.op x₂ :=
begin
  classical,
  let O := [mk f₁, mk f₂].to_finset,
  let f₁' : O := ⟨mk f₁, by simp⟩,
  let f₂' : O := ⟨mk f₂, by simp⟩,
  apply (ℱ.property _ (factor_cover_sieve H H' O).property).is_separated_for.ext,
  intros Y f hf,
  let H := factor_cover_sieve_factor H H' O hf,
  simp only [← types_comp_apply (ℱ.val.map _) (ℱ.val.map _), ← ℱ.val.map_comp, ← op_comp],
  have e₁ : _ = f ≫ f₁ := H.map_fac' f₁',
  have e₂ : _ = f ≫ f₂ := H.map_fac' f₂',
  simp only [←e₁, ←e₂, op_comp, ℱ.val.map_comp, types_comp_apply],
  congr,
  apply hx (H.premap f₁') (H.premap f₂'),
  simp [H.map_fac f₁', H.map_fac f₂', eq],
end

/--
If a functor is faithful and cover-preserving and cover-dense, then it is compatible-preserving.
-/
def compatible_preserving_of_dense_and_cover_preserving [faithful G] : compatible_preserving K G :=
begin
  split,
  intros ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ eq,
  apply functor_pushforward_compatible_of_dense_subsite H H' ℱ f₁ f₂ _ _ eq,
  intros X' f₁' f₂' eq',
  apply hx,
  apply G.map_injective,
  simpa using eq'
end

end category_theory
