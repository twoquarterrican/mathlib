/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.free
import algebra.lie.quotient
import data.fin.vec_notation
import data.matrix.basic

/-!
# Lie algebras from Cartan matrices

Split semi-simple Lie algebras are uniquely determined by their Cartan matrix. Indeed, if `A` is
an `l × l` Cartan matrix, the corresponding Lie algebra may be obtained as the Lie algebra on
`3l` generators: $H_1, H_2, \ldots H_l, E_1, E_2, \ldots, E_l, F_1, F_2, \ldots, F_l$
subject to the following relations:
$$
\begin{align}
  [H_i, H_j] &= 0\\
  [E_i, F_i] &= H_i\\
  [E_i, F_j] &= 0 \quad\text{if $i \ne j$}\\
  [H_i, E_j] &= A_{ij}E_j\\
  [H_i, F_j] &= -A_{ij}F_j\\
  ad(E_i)^{1 - A_{ij}}(E_j) &= 0 \quad\text{if $i \ne j$}\\
  ad(F_i)^{1 - A_{ij}}(F_j) &= 0 \quad\text{if $i \ne j$}\\
\end{align}
$$

In this file we provide the above construction. It is defined for any square matrix of integers but
the results for non-Cartan matrices should be regarded as junk.

Recall that a Cartan matrix is a square matrix of integers `A` such that:
 * For diagonal values we have: `A i i = 2`.
 * For off-diagonal values (`i ≠ j`) we have: `A i j ∈ {-3, -2, -1, 0}`.
 * `A i j = 0 ↔ A j i = 0`.
 * There exists a diagonal matrix `D` over ℝ such that `D ⬝ A ⬝ D⁻¹` is symmetric positive definite.

## Alternative construction

This construction is sometimes performed within the free unital associative algebra
`free_algebra R X`, rather than within the free Lie algebra `free_lie_algebra R X`, as we do here.
However the difference is illusory since the construction stays inside the Lie subalgebra of
`free_algebra R X` generated by `X`, and this is naturally isomorphic to `free_lie_algebra R X`
(though the proof of this seems to require Poincaré–Birkhoff–Witt).

## Definitions of exceptional Lie algebras

This file also contains the Cartan matrices of the exceptional Lie algebras. By using these in the
above construction, it thus provides definitions of the exceptional Lie algebras. These definitions
make sense over any commutative ring. When the ring is ℝ, these are the split real forms of the
exceptional semisimple Lie algebras.

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*](bourbaki1968) plates V -- IX,
  pages 275--290

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 7--9*](bourbaki1975b) chapter VIII, §4.3

* [J.P. Serre, *Complex Semisimple Lie Algebras*](serre1965) chapter VI, appendix

## Main definitions

  * `matrix.to_lie_algebra`
  * `cartan_matrix.E₆`
  * `cartan_matrix.E₇`
  * `cartan_matrix.E₈`
  * `cartan_matrix.F₄`
  * `cartan_matrix.G₂`
  * `lie_algebra.e₆`
  * `lie_algebra.e₇`
  * `lie_algebra.e₈`
  * `lie_algebra.f₄`
  * `lie_algebra.g₂`

## Tags

lie algebra, semi-simple, cartan matrix
-/

universes u v w

noncomputable theory

variables (R : Type u) {B : Type v} [comm_ring R] [decidable_eq B] [fintype B]
variables (A : matrix B B ℤ)

namespace cartan_matrix

variables (B)

/-- The generators of the free Lie algebra from which we construct the Lie algebra of a Cartan
matrix as a quotient. -/
inductive generators
| H : B → generators
| E : B → generators
| F : B → generators

instance [inhabited B] : inhabited (generators B) := ⟨generators.H $ default B⟩

variables {B}

namespace relations

open function

local notation `H` := free_lie_algebra.of R ∘ generators.H
local notation `E` := free_lie_algebra.of R ∘ generators.E
local notation `F` := free_lie_algebra.of R ∘ generators.F
local notation `ad` := lie_algebra.ad R (free_lie_algebra R (generators B))

/-- The terms correpsonding to the `⁅H, H⁆`-relations. -/
def HH : B × B → free_lie_algebra R (generators B) :=
uncurry $ λ i j, ⁅H i, H j⁆

/-- The terms correpsonding to the `⁅E, F⁆`-relations. -/
def EF : B × B → free_lie_algebra R (generators B) :=
uncurry $ λ i j, if i = j then ⁅E i, F i⁆ - H i else ⁅E i, F j⁆

/-- The terms correpsonding to the `⁅H, E⁆`-relations. -/
def HE : B × B → free_lie_algebra R (generators B) :=
uncurry $ λ i j, ⁅H i, E j⁆ - (A i j) • E j

/-- The terms correpsonding to the `⁅H, F⁆`-relations. -/
def HF : B × B → free_lie_algebra R (generators B) :=
uncurry $ λ i j, ⁅H i, F j⁆ + (A i j) • F j

/-- The terms correpsonding to the `ad E`-relations.

Note that we use `int.to_nat` so that we can take the power and that we do not bother
restricting to the case `i ≠ j` since these relations are zero anyway. We also defensively
ensure this with `ad_E_of_eq_eq_zero`. -/
def ad_E : B × B → free_lie_algebra R (generators B) :=
uncurry $ λ i j, (ad (E i))^(-A i j).to_nat $ ⁅E i, E j⁆

/-- The terms correpsonding to the `ad F`-relations.

See also `ad_E` docstring. -/
def ad_F : B × B → free_lie_algebra R (generators B) :=
uncurry $ λ i j, (ad (F i))^(-A i j).to_nat $ ⁅F i, F j⁆

private lemma ad_E_of_eq_eq_zero (i : B) (h : A i i = 2) : ad_E R A ⟨i, i⟩ = 0 :=
have h' : (-2 : ℤ).to_nat = 0, { refl, },
by simp [ad_E, h, h']

private lemma ad_F_of_eq_eq_zero (i : B) (h : A i i = 2) : ad_F R A ⟨i, i⟩ = 0 :=
have h' : (-2 : ℤ).to_nat = 0, { refl, },
by simp [ad_F, h, h']

/-- The union of all the relations as a subset of the free Lie algebra. -/
def to_set : set (free_lie_algebra R (generators B)) :=
(set.range $ HH R) ∪
(set.range $ EF R) ∪
(set.range $ HE R A) ∪
(set.range $ HF R A) ∪
(set.range $ ad_E R A) ∪
(set.range $ ad_F R A)

/-- The ideal of the free Lie algebra generated by the relations. -/
def to_ideal : lie_ideal R (free_lie_algebra R (generators B)) :=
lie_submodule.lie_span R _ $ to_set R A

end relations

end cartan_matrix

/-- The Lie algebra corresponding to a Cartan matrix.

Note that it is defined for any matrix of integers. Its value for non-Cartan matrices should be
regarded as junk. -/
@[derive [inhabited, lie_ring, lie_algebra R]]
def matrix.to_lie_algebra := (cartan_matrix.relations.to_ideal R A).quotient

namespace cartan_matrix

/-- The Cartan matrix of type e₆. See [bourbaki1968] plate V, page 277.

The corresponding Dynkin diagram is:
```
            o
            |
o --- o --- o --- o --- o
```
-/
def E₆ : matrix (fin 6) (fin 6) ℤ := ![![ 2,  0, -1,  0,  0,  0],
                                       ![ 0,  2,  0, -1,  0,  0],
                                       ![-1,  0,  2, -1,  0,  0],
                                       ![ 0, -1, -1,  2, -1,  0],
                                       ![ 0,  0,  0, -1,  2, -1],
                                       ![ 0,  0,  0,  0, -1,  2]]

/-- The Cartan matrix of type e₇. See [bourbaki1968] plate VI, page 281.

The corresponding Dynkin diagram is:
```
            o
            |
o --- o --- o --- o --- o --- o
```
-/
def E₇ : matrix (fin 7) (fin 7) ℤ := ![![ 2,  0, -1,  0,  0,  0,  0],
                                       ![ 0,  2,  0, -1,  0,  0,  0],
                                       ![-1,  0,  2, -1,  0,  0,  0],
                                       ![ 0, -1, -1,  2, -1,  0,  0],
                                       ![ 0,  0,  0, -1,  2, -1,  0],
                                       ![ 0,  0,  0,  0, -1,  2, -1],
                                       ![ 0,  0,  0,  0,  0, -1,  2]]

/-- The Cartan matrix of type e₈. See [bourbaki1968] plate VII, page 285.

The corresponding Dynkin diagram is:
```
            o
            |
o --- o --- o --- o --- o --- o --- o
```
-/
def E₈ : matrix (fin 8) (fin 8) ℤ := ![![ 2,  0, -1,  0,  0,  0,  0,  0],
                                       ![ 0,  2,  0, -1,  0,  0,  0,  0],
                                       ![-1,  0,  2, -1,  0,  0,  0,  0],
                                       ![ 0, -1, -1,  2, -1,  0,  0,  0],
                                       ![ 0,  0,  0, -1,  2, -1,  0,  0],
                                       ![ 0,  0,  0,  0, -1,  2, -1,  0],
                                       ![ 0,  0,  0,  0,  0, -1,  2, -1],
                                       ![ 0,  0,  0,  0,  0,  0, -1,  2]]

/-- The Cartan matrix of type f₄. See [bourbaki1968] plate VIII, page 288.

The corresponding Dynkin diagram is:
```
o --- o =>= o --- o
```
-/
def F₄ : matrix (fin 4) (fin 4) ℤ := ![![ 2, -1,  0,  0],
                                       ![-1,  2, -2,  0],
                                       ![ 0, -1,  2, -1],
                                       ![ 0,  0, -1,  2]]

/-- The Cartan matrix of type g₂. See [bourbaki1968] plate IX, page 290.

The corresponding Dynkin diagram is:
```
o ≡>≡ o
```
Actually we are using the transpose of Bourbaki's matrix. This is to make this matrix consistent
with `cartan_matrix.F₄`, in the sense that all non-zero values below the diagonal are -1. -/
def G₂ : matrix (fin 2) (fin 2) ℤ := ![![ 2, -3],
                                       ![-1,  2]]

end cartan_matrix

namespace lie_algebra

/-- The exceptional split Lie algebra of type e₆. -/
abbreviation e₆ := cartan_matrix.E₆.to_lie_algebra R

/-- The exceptional split Lie algebra of type e₇. -/
abbreviation e₇ := cartan_matrix.E₇.to_lie_algebra R

/-- The exceptional split Lie algebra of type e₈. -/
abbreviation e₈ := cartan_matrix.E₈.to_lie_algebra R

/-- The exceptional split Lie algebra of type f₄. -/
abbreviation f₄ := cartan_matrix.F₄.to_lie_algebra R

/-- The exceptional split Lie algebra of type g₂. -/
abbreviation g₂ := cartan_matrix.G₂.to_lie_algebra R

end lie_algebra
