/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import topology.homotopy.product
import topology.homotopy.equiv
import topology.homotopy.casts
import category_theory.equivalence

/-!
# Homotopic maps induce naturally isomorphic functors

## Main definitions

  - `fundamental_groupoid_functor.homotopic_maps_nat_iso H` The natural isomorphism
    between the induced functors `f : π(X) ⥤ π(Y)` and `g : π(X) ⥤ π(Y)`, given a homotopy
    `H : f ∼ g`

  - `fundamental_groupoid_functor.equiv_of_homotopy_equiv hequiv` The equivalence of the categories
    `π(X)` and `π(Y)` given a homotopy equivalence `hequiv : X ≃ₕ Y` between them.

## Implementation notes
  - In order to be more universe polymorphic, we define `continuous_map.homotopy.ulift_map`
  which lifts a homotopy from `I × X → Y` to `(Top.of ((ulift I) × X)) → Y`
-/

noncomputable theory

universe u

namespace unit_interval
open_locale unit_interval

/-- The path 0 ⟶ 1 in I -/
def path01 : path (0 : I) 1 := { to_fun := id, source' := rfl, target' := rfl }

/-- The path 0 ⟶ 1 in ulift I -/
def upath01 : path (ulift.up 0 : ulift.{u} I) (ulift.up 1) :=
{ to_fun := ulift.up, source' := rfl, target' := rfl }

local attribute [instance] path.homotopic.setoid
/-- The homotopy path class of 0 → 1 in `ulift I` -/
def uhpath01 := @fundamental_groupoid.from_path (Top.of $ ulift.{u} I) _ _ ⟦upath01⟧

end unit_interval

namespace continuous_map.homotopy
open fundamental_groupoid
open category_theory
open unit_interval (uhpath01)
open fundamental_groupoid_functor

open_locale fundamental_groupoid
open_locale unit_interval

local attribute [instance] path.homotopic.setoid


/- We let `X` and `Y` be spaces, and `f` and `g` be homotopic maps between them -/
variables {X Y : Top.{u}} {f g : C(X, Y)} (H : continuous_map.homotopy f g)
  {x₀ x₁ : X} (p : from_top x₀ ⟶ x₁)

/-!
These definitions set up the following diagram, for each path `p`:

          f(p)
      *--------*
      | \      |
  H₀  |   \ d  |  H₁
      |     \  |
      *--------*
          g(p)

Here, `H₀ = H.to_path x₀` is the path from `f(x₀)` to `g(x₀)`,
and similarly for `H₁`. Similarly, `f(p)` denotes the
path in Y that the induced map `f` takes `p`, and similarly for `g(p)`.

Finally, `d`, the diagonal path, is H(0 ⟶ 1, p), the result of the induced `H` on
`path.homotopic.prod (0 ⟶ 1) p`, where `(0 ⟶ 1)` denotes the path from `0` to `1` in `I`.

It is clear that the diagram commutes (`H₀ ≫ g(p) = d = f(p) ≫ H₁`), but unfortunately,
many of the paths do not have defeq starting/ending points, so we end up needing some casting.
-/

/-- Interpret a homotopy `H : C(I × X, Y) as a map C(ulift I × X, Y) -/
def ulift_map : C(Top.of (ulift.{u} I × X), Y) :=
⟨λ x, H (x.1.down, x.2),
  H.continuous.comp ((continuous_induced_dom.comp continuous_fst).prod_mk continuous_snd)⟩

@[simp] lemma ulift_apply (i : ulift.{u} I) (x : X) : H.ulift_map (i, x) = H (i.down, x) := rfl

/-- An abbreviation for `prod_to_prod_Top`, with some types already in place to help the
 typechecker. In particular, the first path should be on the ulifted unit interval. -/
abbreviation prod_to_prod_Top_I {a₁ a₂ : Top.of (ulift I)} {b₁ b₂ : X}
  (p₁ : from_top a₁ ⟶ a₂) (p₂ : from_top b₁ ⟶ b₂) :=
@category_theory.functor.map _ _ _ _ (prod_to_prod_Top (Top.of $ ulift I) X)
  (a₁, b₁) (a₂, b₂) (p₁, p₂)

/-- The diagonal path `d` of a homotopy `H` on a path `p` -/
def diagonal_path : from_top (H (0, x₀)) ⟶ H (1, x₁) :=
(πₘ H.ulift_map).map (prod_to_prod_Top_I uhpath01 p)

/-- The diagonal path, but starting from `f x₀` and going to `g x₁` -/
def diagonal_path' : from_top (f x₀) ⟶ g x₁ :=
hcast (H.apply_zero x₀).symm ≫ (H.diagonal_path p) ≫ hcast (H.apply_one x₁)

/-- Proof that `f(p) = H(0 ⟶ 0, p)`, with the appropriate casts -/
lemma apply_zero_path : (πₘ f).map p = hcast (H.apply_zero x₀).symm
  ≫ (πₘ H.ulift_map).map (prod_to_prod_Top_I (𝟙 (ulift.up 0)) p)
  ≫ hcast (H.apply_zero x₁) :=
begin
  apply quotient.induction_on p,
  intro p',
  apply @eq_path_of_eq_image _ _ _ _ H.ulift_map _ _ _ _ _ ((path.refl (ulift.up _)).prod p'),
  simp,
end

/-- Proof that `g(p) = H(1 ⟶ 1, p)`, with the appropriate casts -/
lemma apply_one_path : (πₘ g).map p = hcast (H.apply_one x₀).symm
  ≫ ((πₘ H.ulift_map).map (prod_to_prod_Top_I (𝟙 (ulift.up 1)) p))
  ≫ hcast (H.apply_one x₁) :=
begin
  apply quotient.induction_on p,
  intro p',
  apply @eq_path_of_eq_image _ _ _ _ H.ulift_map _ _ _ _ _ ((path.refl (ulift.up _)).prod p'),
  simp,
end

/-- Proof that `H.to_path x = H(0 ⟶ 1, x ⟶ x)`, with the appropriate casts -/
lemma to_path_eq (x : X) : ⟦H.to_path x⟧ =
  hcast (H.apply_zero x).symm ≫
  (πₘ H.ulift_map).map (prod_to_prod_Top_I uhpath01 (𝟙 x)) ≫
  hcast (H.apply_one x) :=
begin
  dunfold prod_to_prod_Top_I, dunfold uhpath01,
  simp only [id_eq_path_refl, prod_to_prod_Top_map, path.homotopic.prod_lift, map_eq,
    ← path.homotopic.map_lift, path_cast_right, path_cast_left],
  refl,
end

/- Finally, we show `d = f(p) ≫ H₁ = H₀ ≫ g(p)` -/
lemma eq_diag_path :
  (πₘ f).map p ≫ ⟦H.to_path x₁⟧ = H.diagonal_path' p ∧
  (⟦H.to_path x₀⟧ ≫ (πₘ g).map p : from_top (f x₀) ⟶ g x₁) = H.diagonal_path' p :=
begin
  rw [H.apply_zero_path, H.apply_one_path, H.to_path_eq, H.to_path_eq],
  dunfold prod_to_prod_Top_I,
  split;
  { slice_lhs 2 5 { simp [← category_theory.functor.map_comp], }, refl, },
end

end continuous_map.homotopy

namespace fundamental_groupoid_functor
open category_theory
open_locale fundamental_groupoid
local attribute [instance] path.homotopic.setoid

variables {X Y : Top.{u}} {f g : C(X, Y)} (H : continuous_map.homotopy f g)

/-- Given a homotopy H : f ∼ g, we have an associated natural isomorphism between the induced
functors `f` and `g` -/
def homotopic_maps_nat_iso : πₘ f ⟶ πₘ g :=
{ app := λ x, ⟦H.to_path x⟧,
  naturality' := λ x y p, by rw [(H.eq_diag_path p).1, (H.eq_diag_path p).2] }

instance : is_iso (homotopic_maps_nat_iso H) := by apply nat_iso.is_iso_of_is_iso_app

open_locale continuous_map

/-- Homotopy equivalent topological spaces have equivalent fundamental groupoids. -/
def equiv_of_homotopy_equiv (hequiv : X ≃ₕ Y) : (πₓ X).α ≌ (πₓ Y).α :=
begin
  apply equivalence.mk
    (πₘ hequiv.to_fun : (πₓ X).α ⥤ (πₓ Y).α)
    (πₘ hequiv.inv_fun : (πₓ Y).α ⥤ (πₓ X).α);
  simp only [Groupoid.hom_to_functor, Groupoid.id_to_functor],
  { convert (as_iso (homotopic_maps_nat_iso hequiv.left_inv.some)).symm,
    exacts [((π).map_id X).symm, ((π).map_comp _ _).symm] },
  { convert as_iso (homotopic_maps_nat_iso hequiv.right_inv.some),
    exacts [((π).map_comp _ _).symm, ((π).map_id Y).symm] },
end

end fundamental_groupoid_functor
