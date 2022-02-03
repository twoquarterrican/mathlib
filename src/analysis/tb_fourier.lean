import topology.algebra.continuous_monoid_hom
import topology.algebra.uniform_group
import topology.compact_open
import topology.uniform_space.compact_convergence
import topology.continuous_function.algebra
import analysis.complex.circle

--open measure_theory

section continuous_monoid_hom

variables {A B C D E F : Type*}
  [monoid A] [monoid B] [monoid C] [monoid D] [comm_group E] [comm_group F]
  [topological_space A] [topological_space B] [topological_space C] [topological_space D]
  [topological_space E] [topological_group E] [topological_space F] [topological_group F]

namespace continuous_monoid_hom

lemma map_one (f : continuous_monoid_hom A B) : f 1 = 1 :=
f.to_monoid_hom.map_one

lemma map_mul (f : continuous_monoid_hom A B) (a b : A) : f (a * b) = f a * f b :=
f.to_monoid_hom.map_mul a b

open_locale pointwise

lemma is_closed_embedding [has_continuous_mul B] [t2_space B] :
  closed_embedding (to_continuous_map : continuous_monoid_hom A B → C(A, B)) :=
⟨is_embedding A B, ⟨begin
  suffices : (set.range (to_continuous_map : continuous_monoid_hom A B → C(A, B))) =
    ({f | f '' {1} ⊆ {1}ᶜ} ∪ ⋃ (x y) (U V W) (hU : is_open U) (hV : is_open V) (hW : is_open W)
    (h : disjoint (U * V) W), {f | f '' {x} ⊆ U} ∩ {f | f '' {y} ⊆ V} ∩ {f | f '' {x * y} ⊆ W})ᶜ,
  { rw [this, compl_compl],
    refine (continuous_map.is_open_gen is_compact_singleton is_open_compl_singleton).union _,
    repeat { apply is_open_Union, intro, },
    repeat { apply is_open.inter },
    all_goals { apply continuous_map.is_open_gen is_compact_singleton, assumption } },
  simp_rw [set.compl_union, set.compl_Union, set.image_singleton, set.singleton_subset_iff,
    set.ext_iff, set.mem_inter_iff, set.mem_Inter, set.mem_compl_iff],
  refine λ f, ⟨_, _⟩,
  { rintros ⟨f, rfl⟩,
    exact ⟨λ h, h f.map_one, λ x y U V W hU hV hW h ⟨⟨hfU, hfV⟩, hfW⟩,
      h ⟨set.mul_mem_mul hfU hfV, (congr_arg (∈ W) (f.map_mul x y)).mp hfW⟩⟩ },
  { rintros ⟨hf1, hf2⟩,
    suffices : ∀ x y, f (x * y) = f x * f y,
    { exact ⟨continuous_monoid_hom.mk f (of_not_not hf1) this, continuous_map.ext (λ _, rfl)⟩ },
    intros x y,
    specialize hf2 x y,
    contrapose! hf2,
    obtain ⟨UV, W, hUV, hW, hfUV, hfW, h⟩ := t2_separation hf2.symm,
    obtain ⟨U, V, hU, hV, hfU, hfV, h'⟩ :=
    is_open_prod_iff.mp (hUV.preimage (@continuous_mul B _ _ _)) (f x) (f y) hfUV,
    refine ⟨U, V, W, hU, hV, hW, ((disjoint_iff.mpr h).mono_left _), ⟨hfU, hfV⟩, hfW⟩,
    rintros _ ⟨x, y, hx : (x, y).1 ∈ U, hy : (x, y).2 ∈ V, rfl⟩,
    exact h' ⟨hx, hy⟩ },
end⟩⟩

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
