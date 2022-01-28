import topology.algebra.continuous_monoid_hom
import topology.algebra.uniform_group
import topology.compact_open
import topology.uniform_space.compact_convergence
import topology.continuous_function.algebra
import analysis.complex.circle

--open measure_theory

section continuous_monoid_hom

variables (A B C D E F : Type*)
  [monoid A] [monoid B] [monoid C] [monoid D] [comm_group E] [comm_group F]
  [topological_space A] [topological_space B] [topological_space C] [topological_space D]
  [topological_space E] [topological_group E] [topological_space F] [topological_group F]

namespace continuous_monoid_hom

lemma is_closed_embedding :
  closed_embedding (to_continuous_map : continuous_monoid_hom A B → C(A, B)) :=
⟨is_embedding A B, begin
  -- complement is covered by `{f(x)=a,f(y)=b,f(z)=c}` for fixed `x * y = z` and `a * b ≠ c`.
  -- Now find open neighborhoods `U,V,W` of `a,b,c` with `U * V ∩ W = ∅`.
  -- Then use compact open topology to finish.
  sorry
end⟩

-- https://math.stackexchange.com/questions/1502405/why-is-the-pontraygin-dual-a-locally-compact-group
-- https://math.stackexchange.com/questions/2622521/pontryagin-dual-group-inherits-local-compactness

variables {A B C D E F}

def swap_args : continuous_monoid_hom (continuous_monoid_hom A (continuous_monoid_hom B E))
  (continuous_monoid_hom B (continuous_monoid_hom A E)) :=
begin
  sorry
end

def eval : continuous_monoid_hom A (continuous_monoid_hom (continuous_monoid_hom A E) E) :=
swap_args (id (continuous_monoid_hom A E))

#check monoid_hom.comp_hom
#check monoid_hom.comp_hom'

/-def covariant : continuous_monoid_hom (continuous_monoid_hom E F)
  (continuous_monoid_hom (continuous_monoid_hom A E) (continuous_monoid_hom A F)) :=
begin
  sorry
end

def contravariant (f : continuous_monoid_hom A B) :
  continuous_monoid_hom (continuous_monoid_hom B E) (continuous_monoid_hom A E) :=
begin
  sorry
end

def contravariant' : continuous_monoid_hom (continuous_monoid_hom A E)
  (continuous_monoid_hom (continuous_monoid_hom E F) (continuous_monoid_hom A F)) :=
begin
  sorry
end-/

end continuous_monoid_hom

end continuous_monoid_hom

section pontryagin_dual

variables (G H : Type*) [monoid G] [monoid H] [topological_space G] [topological_space H]

def pontryagin_dual := continuous_monoid_hom G circle

namespace pontryagin_dual

noncomputable instance : has_coe_to_fun (pontryagin_dual G) (λ _, G → circle) :=
⟨continuous_monoid_hom.to_fun⟩

@[ext] lemma ext {χ ψ : pontryagin_dual G} (h : ∀ g, χ g = ψ g) : χ = ψ :=
continuous_monoid_hom.ext h

noncomputable instance : topological_space (pontryagin_dual G) :=
continuous_monoid_hom.topological_space

instance [locally_compact_space G] : t2_space (pontryagin_dual G) :=
continuous_monoid_hom.t2_space

-- Needs `comm_group circle` instance
noncomputable instance : comm_group (pontryagin_dual G) :=
continuous_monoid_hom.comm_group

instance : topological_group (pontryagin_dual G) :=
continuous_monoid_hom.topological_group

variables {G H}

noncomputable def curry : continuous_monoid_hom (pontryagin_dual (G × H))
  (continuous_monoid_hom G (pontryagin_dual H)) :=
continuous_monoid_hom.curry

/-noncomputable def curry' : continuous_monoid_hom (pontryagin_dual (G × H))
  (continuous_monoid_hom H (pontryagin_dual G)) :=
continuous_monoid_hom.curry'-/

noncomputable def uncurry : continuous_monoid_hom (continuous_monoid_hom G (pontryagin_dual H))
  (pontryagin_dual (G × H)) :=
continuous_monoid_hom.uncurry

/-noncomputable def uncurry' : continuous_monoid_hom (continuous_monoid_hom G (pontryagin_dual H))
  (pontryagin_dual (H × G)) :=
continuous_monoid_hom.uncurry'-/

noncomputable def swap : continuous_monoid_hom (continuous_monoid_hom G (pontryagin_dual H))
  (continuous_monoid_hom H (pontryagin_dual G)) :=
begin
  refine curry.comp _,
  refine continuous_monoid_hom.comp _ uncurry,
  refine continuous_monoid_hom.curry _,
  refine continuous_monoid_hom.comp _(continuous_monoid_hom.swap _ _),
  refine continuous_monoid_hom.uncurry _,
  refine continuous_monoid_hom.comp _(continuous_monoid_hom.swap _ _),
  refine continuous_monoid_hom.curry _,
  refine continuous_monoid_hom.comp _(continuous_monoid_hom.swap _ _),
  refine continuous_monoid_hom.uncurry _,
  exact continuous_monoid_hom.id (pontryagin_dual (G × H)),
end

noncomputable def double_dual : continuous_monoid_hom G (pontryagin_dual (pontryagin_dual G)) :=
begin
  refine swap (continuous_monoid_hom.id (pontryagin_dual G)),
end
-- curry (uncurry' (continuous_monoid_hom.id (pontryagin_dual G)))

variables {A : Type*} [comm_group A] [topological_space A] [topological_group A]

noncomputable def dualize : continuous_monoid_hom (continuous_monoid_hom G A)
  (continuous_monoid_hom (pontryagin_dual A) (pontryagin_dual G)) :=
begin
  refine swap.comp _,
  refine continuous_monoid_hom.curry _,
  refine double_dual.comp _,
  refine continuous_monoid_hom.uncurry _,
  exact continuous_monoid_hom.id (continuous_monoid_hom G A),
end

/-noncomputable def double_dual' : continuous_monoid_hom G (pontryagin_dual (pontryagin_dual G)) :=
{ to_fun := λ g,
  { to_fun := λ χ, χ g,
    map_one' := rfl,
    map_mul' := λ χ ψ, rfl,
    continuous_to_fun := sorry },
  map_one' := continuous_monoid_hom.ext (λ χ, χ.to_monoid_hom.map_one),
  map_mul' := λ g h, continuous_monoid_hom.ext (λ χ, χ.to_monoid_hom.map_mul g h),
  continuous_to_fun := sorry }-/

end pontryagin_dual

end pontryagin_dual

section measures

variables (A B C : Type*)
  [comm_group A] [comm_group B] [comm_group C]
  [topological_space A] [topological_space B] [topological_space C]
  [topological_group A] [topological_group B] [topological_group C]
  [measurable_space A] [measurable_space B] [measurable_space C]
  (μ : measure A) (ν : measure B) (ξ : measure C)
  [measure.is_haar_measure μ] [measure.is_haar_measure ν] [measure.is_haar_measure ξ]

end measures
