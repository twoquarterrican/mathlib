import analysis.fourier
import topology.algebra.continuous_monoid_hom
import topology.algebra.uniform_group
import topology.compact_open
import topology.uniform_space.compact_convergence

open measure_theory

section temp

open_locale classical uniformity topological_space filter

open filter set

variables {G : Type*} [comm_group G] [topological_space G] [topological_group G]

/-lemma topological_group.tends_uniformly_to
  {ι α : Type*} (F : ι → α → G) (f : α → G) (p : filter ι) (s : set α) :
  @tendsto_uniformly_on α G ι (topological_group.to_uniform_space G) F f p s
    ↔ ∀ u ∈ nhds (1 : G), {i : ι | ∀ a ∈ s, F i a / f a ∈ u} ∈ p :=
⟨λ h u hu, h _ ⟨u, hu, set.subset.rfl⟩, λ h v ⟨u, hu, hv⟩,
  p.sets_of_superset (h u hu) (λ i hi a ha, hv (by exact hi a ha))⟩

lemma topological_group.tends_uniformly_to_mul
  {ι₁ ι₂ α : Type*} (F₁ : ι₁ → α → G) (F₂ : ι₂ → α → G)
  (f₁ : α → G) (f₂ : α → G) (p₁ : filter ι₁) (p₂ : filter ι₂) (s : set α)
  (h₁ : @tendsto_uniformly_on α G ι₁ (topological_group.to_uniform_space G) F₁ f₁ p₁ s)
  (h₂ : @tendsto_uniformly_on α G ι₂ (topological_group.to_uniform_space G) F₂ f₂ p₂ s) :
  @tendsto_uniformly_on α G (ι₁ × ι₂) (topological_group.to_uniform_space G)
    (λ i, F₁ i.1 * F₂ i.2) (f₁ * f₂) (p₁.prod p₂) s :=
begin
  rw topological_group.tends_uniformly_to at *,
  intros u hu,
  obtain ⟨v, hv, w, hw, h⟩ := mem_nhds_prod_iff.mp (mem_map.mp
    (continuous_mul.tendsto' ((1 : G), (1 : G)) (1 : G) (one_mul (1 : G)) hu)),
  exact filter.mem_prod_iff.mpr ⟨_, h₁ v hv, _, h₂ w hw, λ x hx a ha, (congr_arg (∈ u)
    (div_mul_comm _ _ _ _)).mp (prod_subset_iff.mp h _ (hx.1 a ha) _ (hx.2 a ha))⟩,
end

lemma topological_group.tends_uniformly_to_inv {ι α : Type*} (F : ι → α → G)
  (f : α → G) (p : filter ι) (s : set α)
  (h : @tendsto_uniformly_on α G ι (topological_group.to_uniform_space G) F f p s) :
  @tendsto_uniformly_on α G ι (topological_group.to_uniform_space G)
    (λ i, (F i)⁻¹) f⁻¹ p s :=
begin
  rw topological_group.tends_uniformly_to at *,
  intros u hu,
  convert h (has_inv.inv ⁻¹' u) (continuous_inv.tendsto' (1 : G) (1 : G) one_inv hu),
  simp only [pi.inv_apply, inv_div_inv, set.mem_preimage, inv_div'],
end-/

instance {X : Type*} [topological_space X] : topological_group (continuous_map X G) :=
{ continuous_mul :=
  begin
    letI : uniform_space G := topological_group.to_uniform_space G,
    rw continuous_iff_continuous_at,
    rintros ⟨f, g⟩,
    rw [continuous_at, continuous_map.tendsto_iff_forall_compact_tendsto_uniformly_on],
    -- `tendsto_iff_forall_compact_tendsto_uniformly_on` or `tendsto_of_tendsto_locally_uniformly`
    intros K hK,
    rw [nhds_prod_eq],
    apply topological_group.tends_uniformly_to_mul,
    { revert K,
      rw ← continuous_map.tendsto_iff_forall_compact_tendsto_uniformly_on,
      exact filter.tendsto_id },
    { revert K,
      rw ← continuous_map.tendsto_iff_forall_compact_tendsto_uniformly_on,
      exact filter.tendsto_id },
  end,
  continuous_inv :=
  begin
    letI : uniform_space G := topological_group.to_uniform_space G,
    rw continuous_iff_continuous_at,
    intro f,
    rw [continuous_at, continuous_map.tendsto_iff_forall_compact_tendsto_uniformly_on],
    intros K hK,
    apply topological_group.tends_uniformly_to_inv,
    revert K,
    rw ← continuous_map.tendsto_iff_forall_compact_tendsto_uniformly_on,
    exact filter.tendsto_id,
  end }

end temp

section continuous_monoid_hom

variables (A B C D E F : Type*)
  [monoid A] [monoid B] [monoid C] [monoid D] [comm_group E] [comm_group F]
  [topological_space A] [topological_space B] [topological_space C] [topological_space D]
  [topological_space E] [topological_group E] [topological_space F] [topological_group F]

namespace continuous_monoid_hom

instance : topological_space (continuous_monoid_hom A B) :=
topological_space.induced to_continuous_map continuous_map.compact_open

lemma is_inducing : inducing (to_continuous_map : continuous_monoid_hom A B → C(A, B)) := ⟨rfl⟩

lemma is_embedding : embedding (to_continuous_map : continuous_monoid_hom A B → C(A, B)) :=
⟨is_inducing A B, λ _ _, ext ∘ continuous_map.ext_iff.mp⟩

lemma is_closed_embedding :
  closed_embedding (to_continuous_map : continuous_monoid_hom A B → C(A, B)) :=
⟨is_embedding A B, begin
  -- complement is covered by `{f(x)=a,f(y)=b,f(z)=c}` for fixed `x * y = z` and `a * b ≠ c`.
  -- Now find open neighborhoods `U,V,W` of `a,b,c` with `U * V ∩ W = ∅`.
  -- Then use compact open topology to finish.
  sorry
end⟩

instance [locally_compact_space A] [t2_space B] : t2_space (continuous_monoid_hom A B) :=
(is_embedding A B).t2_space

-- https://math.stackexchange.com/questions/1502405/why-is-the-pontraygin-dual-a-locally-compact-group
-- https://math.stackexchange.com/questions/2622521/pontryagin-dual-group-inherits-local-compactness


instance : topological_group (continuous_monoid_hom A E) :=
let hi := is_inducing A E, hc := hi.continuous in
{ continuous_mul := hi.continuous_iff.mpr (continuous_mul.comp (continuous.prod_map hc hc)),
  continuous_inv := hi.continuous_iff.mpr (continuous_inv.comp hc) }

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
continuous_monoid_hom.topological_space G circle

instance [locally_compact_space G] : t2_space (pontryagin_dual G) :=
continuous_monoid_hom.t2_space G circle

-- Needs `comm_group circle` instance
noncomputable instance : comm_group (pontryagin_dual G) :=
continuous_monoid_hom.comm_group

instance : topological_group (pontryagin_dual G) :=
continuous_monoid_hom.topological_group G circle

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
