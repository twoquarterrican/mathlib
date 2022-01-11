import analysis.fourier
import topology.compact_open
import topology.uniform_space.compact_convergence

open measure_theory

section temp

open_locale classical uniformity topological_space filter

open filter set

variables {G : Type*} [comm_group G] [topological_space G] [topological_group G]

variable (G)
/-- The right uniformity on a topological group. -/
def topological_group.to_uniform_space : uniform_space G :=
{ uniformity          := comap (λp:G×G, p.2 / p.1) (𝓝 1),
  refl                :=
    by refine map_le_iff_le_comap.1 (le_trans _ (pure_le_nhds 1));
      simp [set.subset_def] {contextual := tt},
  symm                :=
  begin
    suffices : tendsto ((λp, p⁻¹) ∘ (λp:G×G, p.2 / p.1)) (comap (λp:G×G, p.2 / p.1) (𝓝 1)) (𝓝 (1⁻¹)),
    { simpa [(∘), tendsto_comap_iff] },
    exact tendsto.comp (tendsto.inv tendsto_id) tendsto_comap
  end,
  comp                :=
  begin
    intros D H,
    rw mem_lift'_sets,
    { rcases H with ⟨U, U_nhds, U_sub⟩,
      rcases exists_nhds_one_split U_nhds with ⟨V, ⟨V_nhds, V_sum⟩⟩,
      existsi ((λp:G×G, p.2 / p.1) ⁻¹' V),
      have H : (λp:G×G, p.2 / p.1) ⁻¹' V ∈ comap (λp:G×G, p.2 / p.1) (𝓝 (1 : G)),
        by existsi [V, V_nhds] ; refl,
      existsi H,
      have comp_rel_sub :
        comp_rel ((λp:G×G, p.2 / p.1) ⁻¹' V) ((λp, p.2 / p.1) ⁻¹' V) ⊆ (λp:G×G, p.2 / p.1) ⁻¹' U,
      begin
        intros p p_comp_rel,
        rcases p_comp_rel with ⟨z, ⟨Hz1, Hz2⟩⟩,
        simpa [sub_eq_add_neg, add_comm, add_left_comm] using V_sum _ Hz1 _ Hz2
      end,
      exact set.subset.trans comp_rel_sub U_sub },
    { exact monotone_comp_rel monotone_id monotone_id }
  end,
  is_open_uniformity  :=
  begin
    intro S,
    let S' := λ x, {p : G × G | p.1 = x → p.2 ∈ S},
    show is_open S ↔ ∀ (x : G), x ∈ S → S' x ∈ comap (λp:G×G, p.2 / p.1) (𝓝 (1 : G)),
    rw [is_open_iff_mem_nhds],
    refine forall_congr (assume a, forall_congr (assume ha, _)),
    rw [← nhds_translation_div, mem_comap, mem_comap],
    refine exists_congr (assume t, exists_congr (assume ht, _)),
    show (λ (y : G), y / a) ⁻¹' t ⊆ S ↔ (λ (p : G × G), p.snd / p.fst) ⁻¹' t ⊆ S' a,
    split,
    { rintros h ⟨x, y⟩ hx rfl, exact h hx },
    { rintros h x hx, exact @h (a, x) hx rfl }
  end }

end temp

section continuous_monoid_hom

variables (A B C D E : Type*)
  [monoid A] [monoid B] [monoid C] [monoid D] [comm_group E]
  [topological_space A] [topological_space B] [topological_space C] [topological_space D]
  [topological_space E] [topological_group E]

set_option old_structure_cmd true

structure continuous_monoid_hom extends A →* B, continuous_map A B

namespace continuous_monoid_hom

variables {A B C D E}

instance : has_coe_to_fun (continuous_monoid_hom A B) (λ _, A → B) :=
⟨to_fun⟩

@[ext] lemma ext {f g : continuous_monoid_hom A B} (h : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr; exact funext h

def mk' (f : A →* B) (hf : continuous f) : continuous_monoid_hom A B := { .. f }

def comp (g : continuous_monoid_hom B C) (f : continuous_monoid_hom A B) :
  continuous_monoid_hom A C :=
mk' (g.to_monoid_hom.comp f.to_monoid_hom) (g.continuous_to_fun.comp f.continuous_to_fun)

def prod (f : continuous_monoid_hom A B) (g : continuous_monoid_hom A C) :
  continuous_monoid_hom A (B × C) :=
mk' (f.to_monoid_hom.prod g.to_monoid_hom) (f.continuous_to_fun.prod_mk g.continuous_to_fun)

def prod_map (f : continuous_monoid_hom A C) (g : continuous_monoid_hom B D) :
  continuous_monoid_hom (A × B) (C × D) :=
mk' (f.to_monoid_hom.prod_map g.to_monoid_hom) (f.continuous_to_fun.prod_map g.continuous_to_fun)

variables (A B C D E)

def one : continuous_monoid_hom A B := mk' 1 continuous_const

def id : continuous_monoid_hom A A := mk' (monoid_hom.id A) continuous_id

def fst : continuous_monoid_hom (A × B) A := mk' (monoid_hom.fst A B) continuous_fst

def snd : continuous_monoid_hom (A × B) B := mk' (monoid_hom.snd A B) continuous_snd

def inl : continuous_monoid_hom A (A × B) := prod (id A) (one A B)

def inr : continuous_monoid_hom B (A × B) := prod (one B A) (id B)

def diag : continuous_monoid_hom A (A × A) := prod (id A) (id A)

def prod_mul : continuous_monoid_hom (E × E) E :=
mk' mul_monoid_hom continuous_mul

def inv : continuous_monoid_hom E E :=
mk' comm_group.inv_monoid_hom continuous_inv

variables {A B C D E}

def coprod (f : continuous_monoid_hom A E) (g : continuous_monoid_hom B E) :
  continuous_monoid_hom (A × B) E :=
(prod_mul E).comp (f.prod_map g)

variables (A B C D E)

instance : comm_group (continuous_monoid_hom A E) :=
{ mul := λ f g, (prod_mul E).comp (f.prod g),
  mul_comm := λ f g, ext (λ x, mul_comm (f x) (g x)),
  mul_assoc := λ f g h, ext (λ x, mul_assoc (f x) (g x) (h x)),
  one := one A E,
  one_mul := λ f, ext (λ x, one_mul (f x)),
  mul_one := λ f, ext (λ x, mul_one (f x)),
  inv := λ f, (inv E).comp f,
  mul_left_inv := λ f, ext (λ x, mul_left_inv (f x)) }

instance : topological_space (continuous_monoid_hom A B) :=
topological_space.induced to_continuous_map continuous_map.compact_open

lemma is_inducing : inducing (to_continuous_map : continuous_monoid_hom A B → C(A, B)) := ⟨rfl⟩

lemma is_embedding : embedding (to_continuous_map : continuous_monoid_hom A B → C(A, B)) :=
⟨is_inducing A B, λ _ _, ext ∘ continuous_map.ext_iff.mp⟩

instance [locally_compact_space A] [t2_space B] : t2_space (continuous_monoid_hom A B) :=
(is_embedding A B).t2_space

variables {A B C D E}

lemma topological_group.tends_uniformly_to
  {ι α : Type*} (F : ι → α → E) (f : α → E) (p : filter ι) (s : set α) :
  @tendsto_uniformly_on α E ι (topological_group.to_uniform_space E) F f p s
    ↔ ∀ u ∈ nhds (1 : E), {i : ι | ∀ a ∈ s, F i a / f a ∈ u} ∈ p :=
⟨λ h u hu, h _ ⟨u, hu, set.subset.rfl⟩, λ h v ⟨u, hu, hv⟩,
  p.sets_of_superset (h u hu) (λ i hi a ha, hv (by exact hi a ha))⟩

lemma topological_group.tends_uniformly_to_mul
  {ι₁ ι₂ α : Type*} (F₁ : ι₁ → α → E) (F₂ : ι₂ → α → E)
  (f₁ : α → E) (f₂ : α → E) (p₁ : filter ι₁) (p₂ : filter ι₂) (s : set α)
  (h₁ : @tendsto_uniformly_on α E ι₁ (topological_group.to_uniform_space E) F₁ f₁ p₁ s)
  (h₂ : @tendsto_uniformly_on α E ι₂ (topological_group.to_uniform_space E) F₂ f₂ p₂ s) :
  @tendsto_uniformly_on α E (ι₁ × ι₂) (topological_group.to_uniform_space E)
    (λ i, F₁ i.1 * F₂ i.2) (f₁ * f₂) (p₁.prod p₂) s :=
begin
  rw topological_group.tends_uniformly_to at *,
  intros u hu,
  have := continuous_mul.tendsto' ((1 : E), (1 : E)) (1 : E) (one_mul (1 : E)) hu,
  obtain ⟨v, hv, w, hw, h⟩ := mem_nhds_prod_iff.mp this,
  refine filter.mem_prod_iff.mpr ⟨_, h₁ v hv, _, h₂ w hw, _⟩,
  intros x hx a ha,
  suffices : (F₁ x.1 a / f₁ a) * (F₂ x.2 a / f₂ a) ∈ u,
  { -- todo: clean this up?
    rwa [div_mul_eq_mul_div', mul_div, div_div, mul_comm (f₂ a) (f₁ a)] at this },
  exact h (show (F₁ x.1 a / f₁ a, F₂ x.2 a / f₂ a) ∈ v.prod w, from ⟨hx.1 a ha, hx.2 a ha⟩),
end

lemma topological_group.tends_uniformly_to_inv {ι α : Type*} (F : ι → α → E)
  (f : α → E) (p : filter ι) (s : set α)
  (h : @tendsto_uniformly_on α E ι (topological_group.to_uniform_space E) F f p s) :
  @tendsto_uniformly_on α E ι (topological_group.to_uniform_space E)
    (λ i, (F i)⁻¹) f⁻¹ p s :=
begin
  rw topological_group.tends_uniformly_to at *,
  intros u hu,
  specialize h (has_inv.inv ⁻¹' u) (continuous_inv.tendsto' (1 : E) (1 : E) one_inv hu),
  simp_rw [pi.inv_apply, inv_div_inv],
  simp_rw [set.mem_preimage, inv_div'] at h,
  exact h,
end

instance {A : Type*} [topological_space A] : topological_group (continuous_map A E) :=
{ continuous_mul :=
  begin
    letI : uniform_space E := topological_group.to_uniform_space E,
    rw continuous_iff_continuous_at,
    rintros ⟨f, g⟩,
    rw [continuous_at, continuous_map.tendsto_iff_forall_compact_tendsto_uniformly_on],
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
    letI : uniform_space E := topological_group.to_uniform_space E,
    rw continuous_iff_continuous_at,
    intro f,
    rw [continuous_at, continuous_map.tendsto_iff_forall_compact_tendsto_uniformly_on],
    intros K hK,
    apply topological_group.tends_uniformly_to_inv,
    revert K,
    rw ← continuous_map.tendsto_iff_forall_compact_tendsto_uniformly_on,
    exact filter.tendsto_id,
  end }

instance : topological_group (continuous_monoid_hom A E) :=
let hi := is_inducing A E, hc := hi.continuous in
{ continuous_mul := hi.continuous_iff.mpr (continuous_mul.comp (continuous.prod_map hc hc)),
  continuous_inv := hi.continuous_iff.mpr (continuous_inv.comp hc) }

end continuous_monoid_hom

end continuous_monoid_hom

section pontryagin_dual

variables (G : Type*) [monoid G] [topological_space G]

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

-- Temporary comm_group instance
instance : comm_group circle :=
{ mul_comm := λ a b, subtype.ext (mul_comm a b),
  .. circle.group }

-- Needs `comm_group circle` instance
noncomputable instance : comm_group (pontryagin_dual G) :=
continuous_monoid_hom.comm_group G circle

-- A map G × H → circle gives maps H → dual(G) and G → dual(H)
-- Conversely, maps H → dual(G) and G → dual(H) give a map G × H → circle
-- The question is: how does continuity work here?

noncomputable def double_dual : continuous_monoid_hom G (pontryagin_dual (pontryagin_dual G)) :=
{ to_fun := λ g,
  { to_fun := λ χ, χ g,
    map_one' := rfl,
    map_mul' := λ χ ψ, rfl,
    continuous_to_fun := sorry },
  map_one' := continuous_monoid_hom.ext (λ χ, χ.to_monoid_hom.map_one),
  map_mul' := λ g h, continuous_monoid_hom.ext (λ χ, χ.to_monoid_hom.map_mul g h),
  continuous_to_fun := sorry }

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
