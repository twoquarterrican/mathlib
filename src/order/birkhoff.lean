/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
import order.atoms
import order.ideal
import topology.subset_properties

/-!
# Birkhoff's representation theorem

-/

open order

variables {α : Type*}

/-! ### Upper and lower sets -/

-- def lower_set (α : Type*) [has_le α] := {carrier : set α // ∀ a ∈ carrier, ∀ b ≤ a, b ∈ carrier}

structure lower_set (α : Type*) [has_le α] :=
(carrier : set α)
(down_closed : ∀ a ∈ carrier, ∀ b ≤ a, b ∈ carrier)

--TODO: Order on lower sets

/-! ### Irreducible and prime elements -/

/-- A sup-irreducible element is a non-bottom element which isn't the supremum of anything smaller.
-/
--TODO: Replace with `¬ is_min a`
def sup_irreducible [semilattice_sup α] [order_bot α] (a : α) : Prop :=
a ≠ ⊥ ∧ ∀ ⦃b c⦄, b ⊔ c = a → b = a ∨ c = a

def inf_irreducible (a : α) : Prop := sorry

/-- A sup-prime element is a non-bottom element which isn't less than the supremum of anything
smaller. -/
--TODO: Replace with `¬ is_min a`
def sup_prime [semilattice_sup α] [order_bot α] (a : α) : Prop :=
∀ ⦃b c⦄, a ≤ b ⊔ c → a ≤ b ∨ a ≤ c

def inf_prime (a : α) : Prop := sorry

lemma sup_prime.sup_irreducible [semilattice_sup α] [order_bot α] {a : α} (ha : sup_prime a) :
  sup_irreducible a :=
sorry

section distrib_lattice
variables [distrib_lattice α] [order_bot α] {a b c : α}

/-- **Birkhoff's theorem**. -/
def birkhoff [fintype α] : lower_set {a : α // sup_irreducible a} ≃o α :=
{ to_fun := _,
  inv_fun := _,
  left_inv := _,
  right_inv := _,
  map_rel_iff' := _ }

end distrib_lattice

/-! ### Priestley spaces -/

/-- A Priestley space is a compact space-/
class is_priestley_space (α : Type*) [has_le α] [topological_space α] extends compact_space α :=
()
