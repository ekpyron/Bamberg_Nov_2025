theory Monadic_AOT
  imports Main
begin

text\<open>We build a model for monadic second order object theory
     (without accounting for hyper-intensionality).\<close>

typedecl w \<comment> \<open>Type of Possible Worlds\<close>

consts w\<^sub>0 :: w \<comment> \<open>Designated Actual World\<close>

type_synonym \<o> = \<open>w \<Rightarrow> bool\<close> \<comment> \<open>Type of Propositions\<close>

typedecl \<omega> \<comment> \<open>Type of Ordinary Urelements\<close>

typedecl \<sigma> \<comment> \<open>Type of Special Urelements\<close>

datatype \<upsilon> = \<omega>\<upsilon> \<omega> | \<sigma>\<upsilon> \<sigma> \<comment> \<open>Type of Urelements\<close>

type_synonym urrel = \<open>\<upsilon> \<Rightarrow> \<o>\<close> \<comment> \<open>Unary Relations among / Properties of Urelements\<close>

type_synonym \<alpha> = \<open>urrel set\<close> \<comment> \<open>Abstract Objects\<close>

datatype \<nu> = \<omega>\<nu> \<omega> | \<alpha>\<nu> \<alpha> \<comment> \<open>Individuals\<close>

consts \<alpha>\<sigma> :: \<open>\<alpha> \<Rightarrow> \<sigma>\<close> \<comment> \<open>Mapping Abstract Objects to Special Urelements\<close>

text\<open>We specifically choose a surjective mapping.\<close>
specification(\<alpha>\<sigma>)
  surj_\<alpha>\<sigma>: \<open>surj \<alpha>\<sigma>\<close>
proof
  have \<open>inj (\<lambda> x . {(\<lambda> u w . case u of \<sigma>\<upsilon> z \<Rightarrow> x = z | _ \<Rightarrow> False)})\<close> (is \<open>inj ?f\<close>)
  proof
    fix x y :: \<sigma>
    assume \<open>{(\<lambda> u w . case u of \<sigma>\<upsilon> z \<Rightarrow> x = z | _ \<Rightarrow> False)} = {(\<lambda> u w . case u of \<sigma>\<upsilon> z \<Rightarrow> y = z | _ \<Rightarrow> False)}\<close>
    hence \<open>(\<lambda> u w . case u of \<sigma>\<upsilon> z \<Rightarrow> x = z | _ \<Rightarrow> False) = (\<lambda> u w . case u of \<sigma>\<upsilon> z \<Rightarrow> y = z | _ \<Rightarrow> False)\<close>
      by (metis some_elem_eq)
    thus \<open>x = y\<close>
      by (metis (full_types) \<upsilon>.simps(6))
  qed
  thus \<open>surj (inv ?f)\<close>
    by (metis inj_imp_surj_inv)
qed

primrec \<nu>\<upsilon> :: \<open>\<nu> \<Rightarrow> \<upsilon>\<close> where \<comment> \<open>Mapping Individuals to Urelements\<close>
  \<open>\<nu>\<upsilon> (\<omega>\<nu> x) = \<omega>\<upsilon> x\<close>
| \<open>\<nu>\<upsilon> (\<alpha>\<nu> x) = \<sigma>\<upsilon> (\<alpha>\<sigma> x)\<close>

text\<open>Our mapping from individuals to urelements inherits the surjectivity.\<close>
lemma surj_\<nu>\<upsilon>: \<open>surj \<nu>\<upsilon>\<close>
  by (metis \<nu>\<upsilon>.simps(1,2) \<upsilon>.exhaust surj_\<alpha>\<sigma> surj_def)

type_synonym 'a \<tau> = \<open>'a option\<close> \<comment> \<open>Terms denote (Some x) or don't denote (None)\<close>
term "(Some x)::'a \<tau>"
term "None::'a \<tau>"

type_synonym \<Pi> = \<open>urrel \<tau>\<close> \<comment> \<open>Type of Unary Relation Terms\<close>
type_synonym \<kappa> = \<open>\<nu> \<tau>\<close> \<comment> \<open>Type of Individual Terms\<close>

text\<open>Exemplification is Function Application after mapping Individuals to Urelements.\<close>
fun Exe :: \<open>\<Pi> \<Rightarrow> \<kappa> \<Rightarrow> \<o>\<close> (\<open>\<lparr>_,_\<rparr>\<close>) where
  \<open>\<lparr>Some F, Some x\<rparr> = F (\<nu>\<upsilon> x)\<close>
| \<open>\<lparr>_,_\<rparr> = (\<lambda> w. False)\<close>

text\<open>Encoding for Abstract Objects is determined by elementhood in the representation set.\<close>
fun Enc :: \<open>\<kappa> \<Rightarrow> \<Pi> \<Rightarrow> \<o>\<close> (\<open>\<lbrace>_,_\<rbrace>\<close>) where
  \<open>\<lbrace>Some (\<alpha>\<nu> x), Some F\<rbrace> = (\<lambda> w . F \<in> x)\<close>
| \<open>\<lbrace>_,_\<rbrace> = (\<lambda>w. False)\<close>

text\<open>Auxiliary special Hilbert-Epsilon indefinite choice operator.\<close>
definition SomeIfExists :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a \<tau>\<close> (binder \<open>SOMEOPT\<close> 100) where
  \<open>SOMEOPT x . \<phi> x \<equiv> (if \<exists> x . \<phi> x then Some (SOME x . \<phi> x) else None)\<close>

lemma SomeOpt_None_simp[simp]: \<open>((SOMEOPT x . \<phi> x) = None) = (\<nexists> x . \<phi> x)\<close>
  by (simp add: SomeIfExists_def)
lemma SomeOpt_Not_None_simp[simp]: \<open>((SOMEOPT x . \<phi> x) \<noteq> None) = (\<exists> x . \<phi> x)\<close>
  by simp

lemma SomeOpt_Some_witness:
  assumes \<open>\<exists> x . \<phi> x\<close>
  obtains r where \<open>SOMEOPT x . \<phi> x = Some r\<close> and \<open>\<phi> r\<close>
  by (simp add: SomeIfExists_def assms someI_ex)

text\<open>Lambda Abstraction becomes a specially defined notion based on indefinite choice.\<close>

definition AOT_Lambda :: \<open>(\<kappa> \<Rightarrow> \<o>) \<Rightarrow> \<Pi>\<close> (binder \<open>\<^bold>\<lambda>\<close> 800) where
  \<open>\<^bold>\<lambda> x . \<phi> x \<equiv> SOMEOPT r . (\<forall> x w . \<phi> (Some x) w = r (\<nu>\<upsilon> x) w)\<close>

text\<open>Auxiliary special definite choice operator.\<close>

definition TheIfExists :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a \<tau>\<close> (binder \<open>THEOPT\<close> 100) where
  \<open>THEOPT x . \<phi> x \<equiv> (if \<exists>! x . \<phi> x then Some (THE x . \<phi> x) else None)\<close>

lemma TheOpt_None_simp[simp]: \<open>((THEOPT x . \<phi> x) = None) = (\<nexists>! x . \<phi> x)\<close>
  by (simp add: TheIfExists_def)
lemma TheOpt_Not_None_simp[simp]: \<open>((THEOPT x . \<phi> x) \<noteq> None) = (\<exists>! x . \<phi> x)\<close>
  by simp

lemma TheOpt_Some_witness:
  assumes \<open>\<exists>! x . \<phi> x\<close>
  obtains r where \<open>THEOPT x . \<phi> x = Some r\<close> and \<open>\<phi> r\<close> and \<open>\<And> s . \<phi> s \<Longrightarrow> s = r\<close>
  by (metis TheIfExists_def assms the_equality)

text\<open>Definite Descriptions\<close>

definition AOT_The :: \<open>(\<kappa> \<Rightarrow> \<o>) \<Rightarrow> \<kappa>\<close> (binder \<open>\<^bold>\<iota>\<close> 850) where
  \<open>\<^bold>\<iota>x . \<phi> x \<equiv> THEOPT x . \<phi> (Some x) w\<^sub>0\<close>

text\<open>Concreteness\<close>

axiomatization concrete\<omega> :: \<open>\<omega> \<Rightarrow> w \<Rightarrow> bool\<close> where
  ordinary_concrete_in_some_world: \<open>\<exists> w . concrete\<omega> x w\<close> and
  contingently_nonconcrete_object: \<open>\<exists> x w . \<not>concrete\<omega> x w\<^sub>0 \<and> concrete\<omega> x w\<close>

primrec concrete\<upsilon> :: \<open>\<upsilon> \<Rightarrow> \<o>\<close> where
  \<open>concrete\<upsilon> (\<omega>\<upsilon> x) = concrete\<omega> x\<close>
| \<open>concrete\<upsilon> (\<sigma>\<upsilon> x) = (\<lambda> _ . False)\<close>

definition Concrete :: \<open>\<Pi>\<close> (\<open>E!\<close>) where
  \<open>Concrete \<equiv> Some concrete\<upsilon>\<close>

lemma True
  \<comment> \<open>Show that our axioms are consistent in a minimal model with two worlds.\<close>
  nitpick[satisfy, user_axioms, show_consts, expect=genuine, card w=2, card \<omega>=1]
  \<comment> \<open>There are no models with only one world.\<close>
  nitpick[satisfy, user_axioms, show_consts, expect=none, card w=1]
  oops

text\<open>Primitive Connectives and Quantifier\<close>

definition AOT_not :: \<open>\<o> \<Rightarrow> \<o>\<close> (\<open>\<^bold>\<not>_\<close>  [840] 840) where
  \<open>\<^bold>\<not>\<phi> \<equiv> \<lambda> w . \<not>\<phi> w\<close>

definition AOT_imp :: \<open>\<o> \<Rightarrow> \<o> \<Rightarrow> \<o>\<close> (infix \<open>\<^bold>\<rightarrow>\<close> 825) where
  \<open>\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> \<lambda> w . \<phi> w \<longrightarrow> \<psi> w\<close>

definition AOT_box :: \<open>\<o> \<Rightarrow> \<o>\<close> (\<open>\<^bold>\<box>_\<close> [830] 850) where
  \<open>\<^bold>\<box>\<phi> \<equiv> \<lambda> w . \<forall> v . \<phi> v\<close>

definition AOT_act :: \<open>\<o> \<Rightarrow> \<o>\<close> (\<open>\<^bold>\<A>_\<close> [830] 850) where
  \<open>\<^bold>\<A>\<phi> \<equiv> \<lambda> w . \<phi> w\<^sub>0\<close>

definition AOT_all :: \<open>('a \<tau> \<Rightarrow> \<o>) \<Rightarrow> \<o>\<close> (binder \<open>\<^bold>\<forall>\<close> 810) where
  \<open>\<^bold>\<forall>x . \<phi> x \<equiv> \<lambda> w . \<forall> x . \<phi> (Some x) w\<close>

definition AOT_all\<^sub>\<o> :: \<open>(\<o> \<Rightarrow> \<o>) \<Rightarrow> \<o>\<close> (binder \<open>\<^bold>\<forall>\<^sub>\<o>\<close> 810) where
  \<open>\<^bold>\<forall>\<^sub>\<o> p . \<phi> p \<equiv> \<lambda> w . \<forall> p . \<phi> p w\<close>

text\<open>Validity\<close>

definition ValidIn :: \<open>w \<Rightarrow> \<o> \<Rightarrow> bool\<close> (\<open>[_ \<Turnstile> _]\<close>) where
  \<open>[w \<Turnstile> \<phi>] = \<phi> w\<close>

definition ValidNec :: \<open>\<o> \<Rightarrow> bool\<close> (\<open>[\<Turnstile>\<^sub>\<box> _]\<close>) where
  \<open>ValidNec \<phi> \<equiv> (\<forall>w . \<phi> w)\<close>

lemma ValidNec_ValidIn: \<open>[\<Turnstile>\<^sub>\<box> \<phi>] = (\<forall> v . [v \<Turnstile> \<phi>])\<close>
  by (simp add: ValidIn_def ValidNec_def)

definition ValidAct :: \<open>\<o> \<Rightarrow> bool\<close> (\<open>[\<Turnstile> _]\<close>) where
  \<open>ValidAct \<phi> \<equiv> (\<phi> w\<^sub>0)\<close>

lemma ValidAct_ValidIn: \<open>[\<Turnstile> \<phi>] = ([w\<^sub>0 \<Turnstile> \<phi>])\<close>
  by (simp add: ValidAct_def ValidIn_def)

text\<open>Denoting terms (semantic definition)\<close>

definition AOT_denotes :: \<open>'a \<tau> \<Rightarrow> \<o>\<close> (\<open>_\<^bold>\<down>\<close> [1000] 900) where
  \<open>\<tau>\<^bold>\<down> \<equiv> (\<lambda> w . \<tau> \<noteq> None)\<close>

definition AOT_denotes\<^sub>\<o> :: \<open>\<o> \<Rightarrow> \<o>\<close> (\<open>_\<^bold>\<down>\<^sub>\<o>\<close> [1000] 900) where
  \<open>\<tau>\<^bold>\<down>\<^sub>\<o> \<equiv> (\<lambda> w . True)\<close>

text\<open>Derived connectives and quantifier.\<close>

definition AOT_ex :: \<open>('a \<tau> \<Rightarrow> \<o>) \<Rightarrow> \<o>\<close> (binder \<open>\<^bold>\<exists>\<close> 810) where
  \<open>\<^bold>\<exists>x . \<phi> x \<equiv> (\<lambda> w . \<exists> x . \<phi> (Some x) w)\<close>

definition AOT_dia :: \<open>\<o> \<Rightarrow> \<o>\<close> (\<open>\<^bold>\<diamond>_\<close> [830] 850) where
  \<open>\<^bold>\<diamond>\<phi> \<equiv> (\<lambda> w . \<exists> v . \<phi> v)\<close>

definition AOT_conj :: \<open>\<o> \<Rightarrow> \<o> \<Rightarrow> \<o>\<close> (infixr \<open>\<^bold>&\<close> 835) where
  \<open>\<phi> \<^bold>& \<psi> \<equiv> \<lambda> w . \<phi> w \<and> \<psi> w\<close>

definition AOT_disj :: \<open>\<o> \<Rightarrow> \<o> \<Rightarrow> \<o>\<close> (infixr \<open>\<^bold>\<or>\<close> 835) where
  \<open>\<phi> \<^bold>\<or> \<psi> \<equiv> \<lambda> w . \<phi> w \<or> \<psi> w\<close>

definition AOT_equiv :: \<open>\<o> \<Rightarrow> \<o> \<Rightarrow> \<o>\<close> (infix \<open>\<^bold>\<equiv>\<close> 820) where
  \<open>\<phi> \<^bold>\<equiv> \<psi> \<equiv> \<lambda> w . \<phi> w = \<psi> w\<close>

definition AOT_identity :: \<open>'a \<tau> \<Rightarrow> 'a \<tau> \<Rightarrow> \<o>\<close> (infix \<open>\<^bold>=\<close> 863) where
  \<open>\<tau> \<^bold>= \<tau>' \<equiv> \<tau>\<^bold>\<down> \<^bold>& \<tau>'\<^bold>\<down> \<^bold>& (\<lambda>w . \<tau> = \<tau>')\<close>

definition AOT_identity\<^sub>\<o> :: \<open>\<o> \<Rightarrow> \<o> \<Rightarrow> \<o>\<close> (infix \<open>\<^bold>=\<^sub>\<o>\<close> 863) where
  \<open>\<phi> \<^bold>=\<^sub>\<o> \<psi> \<equiv> (\<lambda>w . \<phi> = \<psi>)\<close>

definition EquivDef :: \<open>\<o> \<Rightarrow> \<o> \<Rightarrow> bool\<close> (infix \<open>\<equiv>\<^sub>d\<^sub>f\<close> 10) where
  \<open>\<phi> \<equiv>\<^sub>d\<^sub>f \<psi> \<equiv> (\<forall> w . \<phi> w = \<psi> w)\<close>

primrec IdDef :: \<open>'a \<tau> \<Rightarrow> 'a \<tau> \<Rightarrow> bool\<close> (infix \<open>=\<^sub>d\<^sub>f\<close> 10) where
  \<open>(\<tau> =\<^sub>d\<^sub>f (Some \<tau>')) = (\<tau> = Some \<tau>')\<close>
| \<open>(\<tau> =\<^sub>d\<^sub>f None) = (\<tau> = None)\<close>

text\<open>Definitions of being abstract and being ordinary.\<close>

definition Ordinary :: \<open>\<Pi>\<close> (\<open>O!\<close>) where
  \<open>O! \<equiv> \<^bold>\<lambda> x . \<^bold>\<diamond>\<lparr>E!,x\<rparr>\<close>

definition Abstract :: \<open>\<Pi>\<close> (\<open>A!\<close>) where
  \<open>A! \<equiv> \<^bold>\<lambda> x . \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<rparr>\<close>

section\<open>Auxiliary Semantic Statements\<close>

lemma Lambda_denotes: \<open>[w \<Turnstile> (\<^bold>\<lambda> x . \<phi> x)\<^bold>\<down>] = (\<forall> x y . \<nu>\<upsilon> x = \<nu>\<upsilon> y \<longrightarrow> (\<forall> v . [v \<Turnstile> \<phi> (Some x)] = [v \<Turnstile> \<phi> (Some y)]))\<close>
proof
  assume \<open>[w \<Turnstile> (\<^bold>\<lambda> x . \<phi> x)\<^bold>\<down>]\<close>
  hence \<open>\<exists>r. \<forall>x w. \<phi> (Some x) w = r (\<nu>\<upsilon> x) w\<close>
    by (simp add: AOT_Lambda_def AOT_denotes_def ValidIn_def)
  then obtain r where r: \<open>\<phi> (Some x) w = r (\<nu>\<upsilon> x) w\<close> for x w
    by blast
  thus \<open>\<forall>x y. \<nu>\<upsilon> x = \<nu>\<upsilon> y \<longrightarrow> (\<forall>v. [v \<Turnstile> \<phi> (Some x)] = [v \<Turnstile> \<phi> (Some y)])\<close>
    by (auto simp: r ValidIn_def)
next
  assume \<open>\<forall>x y. \<nu>\<upsilon> x = \<nu>\<upsilon> y \<longrightarrow> (\<forall>v. [v \<Turnstile> \<phi> (Some x)] = [v \<Turnstile> \<phi> (Some y)])\<close>
  hence \<open>\<exists>r . \<forall>x w . \<phi> (Some x) w = r (\<nu>\<upsilon> x) w\<close>
    by (auto intro!: exI[where x=\<open>\<lambda> x . \<phi> (Some (inv \<nu>\<upsilon> x))\<close>])
       (meson ValidIn_def f_inv_into_f rangeI)+
  thus \<open>[w \<Turnstile> (\<^bold>\<lambda> x . \<phi> x)\<^bold>\<down>]\<close>
    by (simp add: AOT_Lambda_def AOT_denotes_def ValidIn_def)
qed

lemma Concrete_denotes: \<open>[w \<Turnstile> E!\<^bold>\<down>]\<close>
  by (simp add: AOT_denotes_def Concrete_def ValidIn_def)

lemma Ordinary_denotes: \<open>[w \<Turnstile> O!\<^bold>\<down>]\<close>
  by (simp add: Concrete_def Lambda_denotes Ordinary_def)

lemma Abstract_denotes: \<open>[w \<Turnstile> A!\<^bold>\<down>]\<close>
  by (simp add: Abstract_def Concrete_def Lambda_denotes)

lemma Beta: \<open>[w \<Turnstile> (\<^bold>\<lambda> x . \<phi> x)\<^bold>\<down>] \<Longrightarrow> [w \<Turnstile> \<kappa>\<^bold>\<down>] \<Longrightarrow> [w \<Turnstile> \<lparr>\<^bold>\<lambda>x . \<phi> x, \<kappa>\<rparr>] = [w \<Turnstile> \<phi> \<kappa>]\<close>
proof -
  assume \<open>[w \<Turnstile> (\<^bold>\<lambda> x . \<phi> x)\<^bold>\<down>]\<close>
  then obtain r where r: \<open>(\<^bold>\<lambda> x . \<phi> x) = Some r\<close> and r': \<open>\<forall> x w . r (\<nu>\<upsilon> x) w = \<phi> (Some x) w\<close>
    by (metis (mono_tags, lifting) AOT_Lambda_def AOT_denotes_def SomeIfExists_def SomeOpt_Some_witness ValidIn_def)
  assume \<open>[w \<Turnstile> \<kappa>\<^bold>\<down>]\<close>
  thus \<open>[w \<Turnstile> \<lparr>\<^bold>\<lambda>x . \<phi> x, \<kappa>\<rparr>] = [w \<Turnstile> \<phi> \<kappa>]\<close>
    unfolding r using r'
    by (induct \<kappa>) (auto simp: AOT_Lambda_def AOT_denotes_def ValidIn_def)
qed

lemma Exe_denotes1:
  assumes \<open>[w \<Turnstile> \<lparr>\<Pi>,\<kappa>\<rparr>]\<close>
  obtains F where \<open>\<Pi> = Some F\<close>
  using ValidIn_def assms by fastforce
lemma Exe_denotes2:
  assumes \<open>[w \<Turnstile> \<lparr>\<Pi>,\<kappa>\<rparr>]\<close>
  obtains x where \<open>\<kappa> = Some x\<close>
  using ValidIn_def assms by fastforce

lemma Enc_denotes1:
  assumes \<open>[w \<Turnstile> \<lbrace>\<kappa>,\<Pi>\<rbrace>]\<close>
  obtains F where \<open>\<Pi> = Some F\<close>
  using ValidIn_def assms by fastforce
lemma Enc_denotes2:
  assumes \<open>[w \<Turnstile> \<lbrace>\<kappa>,\<Pi>\<rbrace>]\<close>
  obtains x where \<open>\<kappa> = Some x\<close>
  using ValidIn_def assms by fastforce

lemma Ordinary_sem: \<open>[w \<Turnstile> \<lparr>O!,Some (\<omega>\<nu> x)\<rparr>]\<close>
  by (metis AOT_denotes_def AOT_dia_def Beta Concrete_def Exe.simps(1) Ordinary_def Ordinary_denotes ValidIn_def \<nu>\<upsilon>.simps(1)
      concrete\<upsilon>.simps(1) option.discI ordinary_concrete_in_some_world)
lemma Ordinary_sem':
  assumes \<open>[w \<Turnstile> \<lparr>O!,\<kappa>\<rparr>]\<close>
  obtains x where \<open>\<kappa> = Some (\<omega>\<nu> x)\<close>
  using assms
  by (metis AOT_denotes_def AOT_dia_def Beta Concrete_def Exe.simps(1) Exe_denotes2 Ordinary_def Ordinary_denotes ValidIn_def \<nu>.exhaust
      \<nu>\<upsilon>.simps(2) concrete\<upsilon>.simps(2) option.simps(3))

lemma Abstract_sem: \<open>[w \<Turnstile> \<lparr>A!,Some (\<alpha>\<nu> x)\<rparr>]\<close>
  by (metis AOT_denotes_def AOT_not_def Abstract_def Abstract_denotes Beta Ordinary_def Ordinary_denotes Ordinary_sem' ValidIn_def
      \<nu>.simps(4) option.distinct(1) option.sel)
lemma Abstract_sem': assumes \<open>[w \<Turnstile> \<lparr>A!,\<kappa>\<rparr>]\<close>
  obtains x where \<open>\<kappa> = Some (\<alpha>\<nu> x)\<close>
  using assms
  by (metis AOT_denotes_def AOT_not_def Abstract_def Abstract_denotes Beta Exe_denotes2 Ordinary_def Ordinary_denotes Ordinary_sem
      ValidIn_def \<nu>.exhaust assms is_none_code(2) is_none_simps(1))

section\<open>AOT Definitions\<close>

named_theorems PLM

lemma PLM_18_1[PLM]: \<open>\<phi> \<^bold>& \<psi> \<equiv>\<^sub>d\<^sub>f \<^bold>\<not>(\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<psi>)\<close>
  by (simp add: AOT_conj_def AOT_imp_def AOT_not_def EquivDef_def)

lemma PLM_18_2[PLM]: \<open>\<phi> \<^bold>\<or> \<psi> \<equiv>\<^sub>d\<^sub>f \<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<psi>\<close>
  using AOT_disj_def AOT_imp_def AOT_not_def EquivDef_def by auto

lemma PLM_18_3[PLM]: \<open>\<phi> \<^bold>\<equiv> \<psi> \<equiv>\<^sub>d\<^sub>f (\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>& (\<psi> \<^bold>\<rightarrow> \<phi>)\<close>
  using AOT_conj_def AOT_equiv_def AOT_imp_def EquivDef_def by auto

lemma PLM_18_4[PLM]: \<open>\<^bold>\<exists> x . \<phi> x \<equiv>\<^sub>d\<^sub>f \<^bold>\<not>(\<^bold>\<forall>x . \<^bold>\<not>\<phi> x)\<close>
  by (simp add: AOT_all_def AOT_ex_def AOT_not_def EquivDef_def)

lemma PLM_18_5[PLM]: \<open>\<^bold>\<diamond>\<phi> \<equiv>\<^sub>d\<^sub>f \<^bold>\<not>\<^bold>\<box>\<^bold>\<not>\<phi>\<close>
  by (simp add: AOT_box_def AOT_dia_def AOT_not_def EquivDef_def)

lemma PLM_20_1[PLM]: \<open>\<kappa>\<^bold>\<down> \<equiv>\<^sub>d\<^sub>f \<^bold>\<exists>F . \<lparr>F,\<kappa>\<rparr>\<close>
  by (simp add: AOT_denotes_def EquivDef_def AOT_ex_def AOT_not_def AOT_all_def)
     (induct \<kappa>; auto)

lemma PLM_20_2[PLM]: \<open>\<Pi>\<^bold>\<down> \<equiv>\<^sub>d\<^sub>f \<^bold>\<exists>x . \<lbrace>x,\<Pi>\<rbrace>\<close>
  by (simp add: AOT_denotes_def EquivDef_def AOT_ex_def AOT_not_def AOT_all_def)
     (metis Enc.simps(1,4) insertI1 option.exhaust_sel)

lemma PLM_20_3[PLM]: \<open>p\<^bold>\<down>\<^sub>\<o> \<equiv>\<^sub>d\<^sub>f (\<^bold>\<lambda> x . p)\<^bold>\<down>\<close>
  using AOT_denotes\<^sub>\<o>_def EquivDef_def Lambda_denotes ValidIn_def by force

lemma PLM_22_1[PLM]: \<open>O! =\<^sub>d\<^sub>f (\<^bold>\<lambda>x . \<^bold>\<diamond>\<lparr>E!,x\<rparr>)\<close>
  by (simp add: Ordinary_def combine_options_cases)

lemma PLM_22_2[PLM]: \<open>A! =\<^sub>d\<^sub>f (\<^bold>\<lambda>x . \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<rparr>)\<close>
  by (simp add: Abstract_def combine_options_cases)

lemma PLM_23_1[PLM]: \<open>x \<^bold>= y \<equiv>\<^sub>d\<^sub>f (\<lparr>O!,x\<rparr> \<^bold>& \<lparr>O!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>)) \<^bold>\<or>
                                (\<lparr>A!,x\<rparr> \<^bold>& \<lparr>A!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F . \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>y,F\<rbrace>))\<close>
proof(simp add: EquivDef_def; safe)
  fix w
  assume \<open>(x \<^bold>= y) w\<close>
  then obtain a b where x: \<open>x = Some a\<close> and y: \<open>y = Some b\<close> and a: \<open>a = b\<close>
    by (metis (full_types) AOT_conj_def AOT_denotes_def AOT_identity_def option.exhaust)
  {
    assume \<open>\<exists> u . b = \<omega>\<nu> u\<close>
    then obtain u where u: \<open>b = \<omega>\<nu> u\<close>
      by blast
    have \<open>(\<lparr>O!,x\<rparr> \<^bold>& \<lparr>O!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>)) w\<close>
      unfolding x y a u
      by (simp add: AOT_disj_def AOT_conj_def AOT_box_def AOT_all_def AOT_equiv_def Ordinary_sem[unfolded ValidIn_def])
  }
  moreover {
    assume \<open>\<exists> u . b = \<alpha>\<nu> u\<close>
    then obtain u where u: \<open>b = \<alpha>\<nu> u\<close>
      by blast
    have \<open>(\<lparr>A!,x\<rparr> \<^bold>& \<lparr>A!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F . \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>y,F\<rbrace>)) w\<close>
      unfolding x y a u
      by (simp add: AOT_disj_def AOT_conj_def AOT_box_def AOT_all_def AOT_equiv_def Abstract_sem[unfolded ValidIn_def])
  }
  ultimately show \<open>((\<lparr>O!,x\<rparr> \<^bold>& \<lparr>O!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>)) \<^bold>\<or>
                              (\<lparr>A!,x\<rparr> \<^bold>& \<lparr>A!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F . \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>y,F\<rbrace>))) w\<close>
    by (meson AOT_disj_def \<nu>.exhaust)
next
  fix w :: w
  assume \<open>((\<lparr>O!,x\<rparr> \<^bold>& \<lparr>O!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>)) \<^bold>\<or>
           (\<lparr>A!,x\<rparr> \<^bold>& \<lparr>A!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F . \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>y,F\<rbrace>))) w\<close>
  moreover {
    assume 0: \<open>(\<lparr>O!,x\<rparr> \<^bold>& \<lparr>O!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>)) w\<close>
    then obtain a b where x: \<open>x = Some (\<omega>\<nu> a)\<close> and y: \<open>y = Some (\<omega>\<nu> b)\<close>
      by (metis (no_types, lifting) AOT_conj_def Ordinary_sem' ValidIn_def)
    have 1: \<open>\<forall>(v::w) F. F (\<omega>\<upsilon> a) v \<longleftrightarrow> F (\<omega>\<upsilon> b) v\<close>
      using 0 unfolding x y
      by (auto simp add: AOT_conj_def AOT_box_def AOT_all_def AOT_equiv_def)
    have \<open>(x \<^bold>= y) w\<close>
      unfolding x y
      using 1[THEN spec, THEN spec[where x=\<open>\<lambda> x _ . x = \<omega>\<upsilon> a\<close>]]
      by (simp add: AOT_conj_def AOT_denotes_def AOT_identity_def)
  }
  moreover {
    assume 0: \<open>(\<lparr>A!,x\<rparr> \<^bold>& \<lparr>A!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F . \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>y,F\<rbrace>)) w\<close>
    then obtain a b where x: \<open>x = Some (\<alpha>\<nu> a)\<close> and y: \<open>y = Some (\<alpha>\<nu> b)\<close>
      by (metis AOT_conj_def Abstract_sem' ValidIn_def)
    have \<open>(F \<in> a) = (F \<in> b)\<close> for F
      using 0 unfolding x y by (simp add: AOT_box_def AOT_conj_def AOT_all_def AOT_equiv_def)
    hence a: \<open>a = b\<close>
      by blast
    have \<open>(x \<^bold>= y) w\<close>
      unfolding x y a
      by (simp add: AOT_identity_def AOT_conj_def AOT_denotes_def)
  }
  ultimately show \<open>(x \<^bold>= y) w\<close>
    using AOT_disj_def by fastforce
qed

lemma PLM_23_2: \<open>F \<^bold>= G \<equiv>\<^sub>d\<^sub>f F\<^bold>\<down> \<^bold>& G\<^bold>\<down> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>x . \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>x,G\<rbrace>)\<close>
proof(simp add: EquivDef_def; safe)
  fix w
  assume \<open>(F \<^bold>= G) w\<close>
  thus \<open>(F\<^bold>\<down> \<^bold>& G\<^bold>\<down> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>x. \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>x,G\<rbrace>)) w\<close>
    by (simp add: AOT_all_def AOT_box_def AOT_conj_def AOT_equiv_def AOT_identity_def)
next
  fix w
  assume 0: \<open>(F\<^bold>\<down> \<^bold>& G\<^bold>\<down> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>x. \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>x,G\<rbrace>)) w\<close>
  then obtain r s where F: \<open>F = Some r\<close> and G: \<open>G = Some s\<close>
    by (metis (no_types, lifting) AOT_conj_def AOT_ex_def Enc.elims EquivDef_def PLM_20_2)
  have \<open>\<lbrace>Some (\<alpha>\<nu> {r}),Some r\<rbrace> w = \<lbrace>Some (\<alpha>\<nu> {r}),Some s\<rbrace> w\<close>
    using 0 unfolding F G
    by (smt (verit, del_insts) AOT_all_def AOT_box_def AOT_conj_def AOT_equiv_def)
  hence r: \<open>r = s\<close>
    by simp
  thus \<open>(F \<^bold>= G) w\<close>
    unfolding F G r
    by (simp add: AOT_identity_def AOT_conj_def AOT_denotes_def)
qed

lemma PLM_23_4: \<open>p \<^bold>=\<^sub>\<o> q \<equiv>\<^sub>d\<^sub>f p\<^bold>\<down>\<^sub>\<o> \<^bold>& q\<^bold>\<down>\<^sub>\<o> \<^bold>& (\<^bold>\<lambda>x . p) \<^bold>= (\<^bold>\<lambda> x . q)\<close>
proof -
  {
    fix w
    assume \<open>((\<^bold>\<lambda>x. q)\<^bold>\<down>) w\<close>
    then obtain r where 0: \<open>(\<^bold>\<lambda>x. q) = Some r\<close> and 1: \<open>\<forall> x v . r (\<nu>\<upsilon> x) v = q v\<close>
      by (smt (verit, best) AOT_Lambda_def AOT_denotes_def SomeOpt_None_simp SomeOpt_Some_witness)
    assume \<open>\<^bold>\<lambda>x. p = \<^bold>\<lambda>x. q\<close>
    hence \<open>\<forall> x v . r (\<nu>\<upsilon> x) v = p v\<close>
      unfolding 0
      by (metis "0" "1" AOT_denotes_def Beta ValidIn_def option.simps(3))
    hence \<open>p = q\<close>
      using 1
      by auto
  } note 0 = this
  thus ?thesis
    by (auto simp add: EquivDef_def AOT_identity\<^sub>\<o>_def AOT_conj_def AOT_denotes\<^sub>\<o>_def AOT_identity_def Lambda_denotes[unfolded ValidIn_def])
qed

section\<open>Deriving AOT's Axioms\<close>

lemma PLM_38_1: \<open>[\<Turnstile>\<^sub>\<box> \<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<phi>)]\<close>
  by (simp add: AOT_imp_def ValidNec_def)
lemma PLM_38_2: \<open>[\<Turnstile>\<^sub>\<box> (\<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<chi>)) \<^bold>\<rightarrow> ((\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> \<chi>))]\<close>
  using AOT_imp_def ValidNec_def by auto
lemma PLM_38_3: \<open>[\<Turnstile>\<^sub>\<box> (\<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<psi>) \<^bold>\<rightarrow> ((\<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> \<phi>)]\<close>
  by (simp add: AOT_imp_def AOT_not_def ValidNec_def)

lemma PLM_39_1: \<open>[\<Turnstile>\<^sub>\<box> (\<^bold>\<forall> \<alpha> . \<phi> \<alpha>) \<^bold>\<rightarrow> (\<tau>\<^bold>\<down> \<^bold>\<rightarrow> \<phi> \<tau>)]\<close>
  by (metis AOT_all_def AOT_denotes_def AOT_imp_def ValidNec_def not_None_eq)
lemma PLM_39_1': \<open>[\<Turnstile>\<^sub>\<box> (\<^bold>\<forall>\<^sub>\<o> \<alpha> . \<phi> \<alpha>) \<^bold>\<rightarrow> (\<tau>\<^bold>\<down>\<^sub>\<o> \<^bold>\<rightarrow> \<phi> \<tau>)]\<close>
  by (simp add: AOT_all\<^sub>\<o>_def AOT_imp_def ValidNec_def)

named_theorems PLM_39_2

lemma PLM_39_2_a[PLM_39_2]: \<open>[\<Turnstile>\<^sub>\<box> (Some x)\<^bold>\<down>]\<close>
  by (simp add: AOT_denotes_def ValidNec_def)
lemma PLM_39_2_a'[PLM_39_2]: \<open>[\<Turnstile>\<^sub>\<box> \<phi>\<^bold>\<down>\<^sub>\<o>]\<close>
  by (simp add: AOT_denotes\<^sub>\<o>_def ValidNec_def)

lemma PLM_39_2_lambda_0[PLM_39_2]:
  \<open>[\<Turnstile>\<^sub>\<box> (\<^bold>\<lambda>x . \<phi>)\<^bold>\<down>]\<close>
  using Lambda_denotes ValidIn_def ValidNec_def by auto
lemma PLM_39_2_lambda_1[PLM_39_2]:
  \<open>[\<Turnstile>\<^sub>\<box> (\<^bold>\<lambda>x . \<lparr>F,x\<rparr>)\<^bold>\<down>]\<close>
  unfolding ValidNec_ValidIn Lambda_denotes
  by (metis Exe.simps(1) Exe_denotes1)
lemma PLM_39_2_lambda_2[PLM_39_2]:
  \<open>[\<Turnstile>\<^sub>\<box> (\<^bold>\<lambda>x . \<phi> x)\<^bold>\<down>] \<Longrightarrow> [\<Turnstile>\<^sub>\<box> (\<^bold>\<lambda>x . \<^bold>\<not>\<phi> x)\<^bold>\<down>]\<close>
  unfolding ValidNec_ValidIn Lambda_denotes AOT_not_def
  unfolding ValidIn_def
  by metis
lemma PLM_39_2_lambda_3[PLM_39_2]:
  \<open>[\<Turnstile>\<^sub>\<box> (\<^bold>\<lambda>x . \<phi> x)\<^bold>\<down>] \<Longrightarrow> [\<Turnstile>\<^sub>\<box> (\<^bold>\<lambda>x . \<psi> x)\<^bold>\<down>] \<Longrightarrow> [\<Turnstile>\<^sub>\<box> (\<^bold>\<lambda>x . \<phi> x \<^bold>\<rightarrow> \<psi> x)\<^bold>\<down>]\<close>
  unfolding ValidNec_ValidIn Lambda_denotes AOT_imp_def
  unfolding ValidIn_def
  by metis
lemma PLM_39_2_lambda_4[PLM_39_2]:
  \<open>[\<Turnstile>\<^sub>\<box> (\<^bold>\<lambda>x . \<phi> x)\<^bold>\<down>] \<Longrightarrow> [\<Turnstile>\<^sub>\<box> (\<^bold>\<lambda>x . \<^bold>\<A>\<phi> x)\<^bold>\<down>]\<close>
  unfolding ValidNec_ValidIn Lambda_denotes AOT_act_def
  unfolding ValidIn_def
  by metis
lemma PLM_39_2_lambda_5[PLM_39_2]:
  \<open>[\<Turnstile>\<^sub>\<box> (\<^bold>\<lambda>x . \<phi> x)\<^bold>\<down>] \<Longrightarrow> [\<Turnstile>\<^sub>\<box> (\<^bold>\<lambda>x . \<^bold>\<box>\<phi> x)\<^bold>\<down>]\<close>
  unfolding ValidNec_ValidIn Lambda_denotes AOT_box_def
  unfolding ValidIn_def
  by metis
lemma PLM_39_2_lambda_6[PLM_39_2]:
  \<open>(\<And> y . [\<Turnstile>\<^sub>\<box> (\<^bold>\<lambda>x . \<phi> y x)\<^bold>\<down>]) \<Longrightarrow> [\<Turnstile>\<^sub>\<box> (\<^bold>\<lambda>x . \<^bold>\<forall> y . \<phi> y x)\<^bold>\<down>]\<close>
  unfolding ValidNec_ValidIn Lambda_denotes AOT_all_def
  unfolding ValidIn_def
  by metis
lemma PLM_39_2_lambda_7[PLM_39_2]:
  \<open>(\<And> y . [\<Turnstile>\<^sub>\<box> (\<^bold>\<lambda>x . \<psi> x y)\<^bold>\<down>]) \<Longrightarrow> (\<And> x . [\<Turnstile>\<^sub>\<box> (\<^bold>\<lambda>y . \<psi> x y)\<^bold>\<down>]) \<Longrightarrow> [\<Turnstile>\<^sub>\<box> (\<^bold>\<lambda>x . \<lparr>(\<^bold>\<lambda>y . \<psi> x y),x\<rparr>)\<^bold>\<down>]\<close>
  unfolding ValidNec_ValidIn Lambda_denotes
  unfolding ValidIn_def
  by (smt (verit, ccfv_threshold) Beta Lambda_denotes PLM_39_2_a ValidIn_def ValidNec_def)
lemma PLM_39_2_lambda_8[PLM_39_2]:
  \<open>(\<And> x  . \<phi> x \<equiv>\<^sub>d\<^sub>f \<psi> x) \<Longrightarrow> [\<Turnstile>\<^sub>\<box> (\<^bold>\<lambda>x . \<psi> x)\<^bold>\<down>] \<Longrightarrow> [\<Turnstile>\<^sub>\<box> (\<^bold>\<lambda>x . \<phi> x)\<^bold>\<down>]\<close>
  unfolding ValidNec_ValidIn Lambda_denotes EquivDef_def
  unfolding ValidIn_def
  by blast
(* ... *)

text\<open>Example for showing that a complex lambda-expression denotes:\<close>
lemma "[\<Turnstile>\<^sub>\<box> (\<^bold>\<lambda>x . p \<^bold>\<or> \<^bold>\<diamond>(\<^bold>\<forall>y . \<lparr>F,y\<rparr> \<^bold>\<rightarrow> \<lparr>\<^bold>\<lambda> z . \<lparr>G,z\<rparr> \<^bold>& \<lparr>F,x\<rparr>,x\<rparr>))\<^bold>\<down>]"
  by (rule PLM_39_2 PLM)+

lemma PLM_39_3: \<open>[\<Turnstile>\<^sub>\<box> (\<^bold>\<forall> \<alpha> . \<phi> \<alpha> \<^bold>\<rightarrow> \<psi> \<alpha>) \<^bold>\<rightarrow> ((\<^bold>\<forall> \<alpha> . \<phi> \<alpha>) \<^bold>\<rightarrow> (\<^bold>\<forall> \<alpha> . \<psi> \<alpha>))]\<close>
  by (simp add: AOT_all_def AOT_imp_def ValidNec_def)
lemma PLM_39_3': \<open>[\<Turnstile>\<^sub>\<box> (\<^bold>\<forall>\<^sub>\<o> \<alpha> . \<phi> \<alpha> \<^bold>\<rightarrow> \<psi> \<alpha>) \<^bold>\<rightarrow> ((\<^bold>\<forall>\<^sub>\<o> \<alpha> . \<phi> \<alpha>) \<^bold>\<rightarrow> (\<^bold>\<forall>\<^sub>\<o> \<alpha> . \<psi> \<alpha>))]\<close>
  using AOT_all\<^sub>\<o>_def AOT_imp_def ValidNec_def by presburger

lemma PLM_39_4: \<open>[\<Turnstile>\<^sub>\<box> \<phi> \<^bold>\<rightarrow> (\<^bold>\<forall> \<alpha> . \<phi>)]\<close>
  by (simp add: AOT_all_def AOT_imp_def ValidNec_def)
lemma PLM_39_4': \<open>[\<Turnstile>\<^sub>\<box> \<phi> \<^bold>\<rightarrow> (\<^bold>\<forall>\<^sub>\<o> \<alpha> . \<phi>)]\<close>
  by (simp add: AOT_all\<^sub>\<o>_def AOT_imp_def ValidNec_def)

lemma PLM_39_5_a: \<open>[\<Turnstile>\<^sub>\<box> \<lparr>\<Pi>,\<kappa>\<rparr> \<^bold>\<rightarrow> (\<Pi>\<^bold>\<down> \<^bold>& \<kappa>\<^bold>\<down>)]\<close>
  by (metis AOT_conj_def AOT_imp_def Exe.elims PLM_39_2_a ValidNec_def)
lemma PLM_39_5_b: \<open>[\<Turnstile>\<^sub>\<box> \<lbrace>\<kappa>,\<Pi>\<rbrace> \<^bold>\<rightarrow> (\<Pi>\<^bold>\<down> \<^bold>& \<kappa>\<^bold>\<down>)]\<close>
  by (metis AOT_conj_def AOT_imp_def Enc.elims PLM_39_2_a ValidNec_def)

lemma PLM_41: \<open>[\<Turnstile>\<^sub>\<box> \<alpha> \<^bold>= \<beta> \<^bold>\<rightarrow> (\<phi> \<alpha> \<^bold>\<rightarrow> \<phi> \<beta>)]\<close>
  by (simp add: AOT_conj_def AOT_identity_def AOT_imp_def ValidNec_def)

lemma PLM_43: \<open>[\<Turnstile> \<^bold>\<A>\<phi> \<^bold>\<rightarrow> \<phi>]\<close>
  using AOT_act_def AOT_imp_def ValidAct_def by presburger

lemma PLM_44_1: \<open>[\<Turnstile>\<^sub>\<box> \<^bold>\<A>\<^bold>\<not>\<phi> \<^bold>\<equiv> \<^bold>\<not>\<^bold>\<A>\<phi>]\<close>
  by (simp add: AOT_act_def AOT_equiv_def AOT_not_def ValidNec_def)
lemma PLM_44_2: \<open>[\<Turnstile>\<^sub>\<box> \<^bold>\<A>(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<equiv> \<^bold>\<A>\<phi> \<^bold>\<rightarrow> \<^bold>\<A>\<psi>]\<close>
  by (simp add: AOT_act_def AOT_equiv_def AOT_imp_def ValidNec_def)
lemma PLM_44_3: \<open>[\<Turnstile>\<^sub>\<box> \<^bold>\<A>(\<^bold>\<forall> \<alpha> . \<phi> \<alpha>) \<^bold>\<equiv> (\<^bold>\<forall> \<alpha> . \<^bold>\<A>\<phi> \<alpha>)]\<close>
  by (simp add: AOT_act_def AOT_all_def AOT_equiv_def ValidNec_def)
lemma PLM_44_3': \<open>[\<Turnstile>\<^sub>\<box> \<^bold>\<A>(\<^bold>\<forall>\<^sub>\<o> \<alpha> . \<phi> \<alpha>) \<^bold>\<equiv> (\<^bold>\<forall>\<^sub>\<o> \<alpha> . \<^bold>\<A>\<phi> \<alpha>)]\<close>
  by (simp add: AOT_act_def AOT_all\<^sub>\<o>_def AOT_equiv_def ValidNec_def)
lemma PLM_44_4: \<open>[\<Turnstile>\<^sub>\<box> \<^bold>\<A>\<phi> \<^bold>\<equiv> \<^bold>\<A>\<^bold>\<A>\<phi>]\<close>
  by (simp add: AOT_act_def AOT_equiv_def ValidNec_def)

lemma PLM_45_1: \<open>[\<Turnstile>\<^sub>\<box> \<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> (\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi>)]\<close> \<comment> \<open>K\<close>
  using AOT_box_def AOT_imp_def ValidNec_def by auto
lemma PLM_45_2: \<open>[\<Turnstile>\<^sub>\<box> \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>]\<close> \<comment> \<open>T\<close>
  by (simp add: AOT_box_def AOT_imp_def ValidNec_def)
lemma PLM_45_3: \<open>[\<Turnstile>\<^sub>\<box> \<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>]\<close> \<comment> \<open>5\<close>
  by (simp add: AOT_box_def AOT_dia_def AOT_imp_def ValidNec_def)

lemma PLM_45_4: \<open>[\<Turnstile>\<^sub>\<box> \<^bold>\<diamond>(\<^bold>\<exists>x. \<lparr>E!,x\<rparr> \<^bold>& \<^bold>\<not>\<^bold>\<A>\<lparr>E!,x\<rparr>)]\<close>
proof -
  obtain x w where 0: \<open>concrete\<omega> x w \<and> \<not>concrete\<omega> x w\<^sub>0\<close>
    using contingently_nonconcrete_object by blast
  thus ?thesis
    by (auto simp: AOT_dia_def AOT_ex_def AOT_conj_def AOT_not_def AOT_act_def ValidNec_def Concrete_def intro!: exI[where x=w] exI[where x=\<open>(\<omega>\<nu> x)\<close>])
qed

lemma PLM_46_1: \<open>[\<Turnstile>\<^sub>\<box> \<^bold>\<A>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<A>\<phi>]\<close>
  by (simp add: AOT_act_def AOT_box_def AOT_imp_def ValidNec_def)

lemma PLM_46_2: \<open>[\<Turnstile>\<^sub>\<box> \<^bold>\<box>\<phi> \<^bold>\<equiv> \<^bold>\<A>\<^bold>\<box>\<phi>]\<close>
  by (simp add: AOT_act_def AOT_box_def AOT_equiv_def ValidNec_def)

lemma PLM_47: \<open>[\<Turnstile>\<^sub>\<box> (Some y) \<^bold>= (\<^bold>\<iota>x . \<phi> x) \<^bold>\<equiv> (\<^bold>\<forall>x . \<^bold>\<A>\<phi> x \<^bold>\<equiv> x \<^bold>= (Some y))]\<close>
  apply(auto simp add: AOT_equiv_def ValidNec_def AOT_identity_def AOT_conj_def AOT_denotes_def AOT_all_def AOT_act_def)
      apply (metis (no_types, lifting) AOT_The_def TheOpt_Not_None_simp TheOpt_Some_witness option.distinct(1))
     apply (metis (no_types, lifting) AOT_The_def TheOpt_Not_None_simp TheOpt_Some_witness option.distinct(1))
   apply (simp add: AOT_The_def TheIfExists_def)
  by (metis (no_types, lifting) AOT_The_def TheOpt_Some_witness)

lemma PLM_48_1: \<open>[\<Turnstile>\<^sub>\<box> (\<^bold>\<lambda>x . \<phi> x)\<^bold>\<down> \<^bold>\<rightarrow> (\<^bold>\<lambda>x . \<phi> x) \<^bold>= (\<^bold>\<lambda>y . \<phi> y)]\<close>
  by (simp add: AOT_conj_def AOT_identity_def AOT_imp_def ValidNec_def)

lemma PLM_48_2: \<open>[\<Turnstile>\<^sub>\<box> (\<^bold>\<lambda>x . \<phi> x)\<^bold>\<down> \<^bold>\<rightarrow> (\<lparr>\<^bold>\<lambda>x . \<phi> x,Some x\<rparr> \<^bold>\<equiv> \<phi> (Some x))]\<close>
  using Beta
  by (simp add: ValidNec_ValidIn AOT_imp_def AOT_equiv_def AOT_denotes_def ValidIn_def)

lemma PLM_48_3: \<open>[\<Turnstile>\<^sub>\<box> (\<^bold>\<lambda> x . \<lparr>Some F,x\<rparr>) \<^bold>= Some F]\<close>
proof -
  have \<open>[w \<Turnstile> (\<^bold>\<lambda> x . \<lparr>Some F,x\<rparr>)\<^bold>\<down>]\<close> for w
    using PLM_39_2_lambda_1 ValidNec_ValidIn by blast
  then obtain r where 1: \<open>(\<^bold>\<lambda> x . \<lparr>Some F,x\<rparr>) = Some r\<close> and 2: \<open>r (\<nu>\<upsilon> x) w = \<lparr>Some F,Some x\<rparr> w\<close> for x w
    by (smt (verit, del_insts) AOT_Lambda_def Exe.simps(1) SomeOpt_Some_witness)
  have 3: \<open>F = r\<close>
  proof(rule ext; rule ext)
    fix x w
    obtain u where x: \<open>x = \<nu>\<upsilon> u\<close>
      by (meson surjE surj_\<nu>\<upsilon>)
    show \<open>F x w = r x w\<close>
      unfolding x
      unfolding 2
      by simp
  qed
  have \<open>AOT_Lambda (Exe (Some F)) = Some F\<close>
    unfolding 1
    unfolding 3
    by blast
  thus ?thesis
    by (auto simp add: AOT_identity_def AOT_conj_def AOT_denotes_def ValidNec_def)
qed

lemma PLM_49: \<open>[\<Turnstile>\<^sub>\<box> ((\<^bold>\<lambda>x . \<phi> x)\<^bold>\<down> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>x . \<phi> x \<^bold>\<equiv> \<psi> x)) \<^bold>\<rightarrow> (\<^bold>\<lambda>x . \<psi> x)\<^bold>\<down>]\<close>
  by (simp add: ValidNec_ValidIn AOT_conj_def AOT_imp_def ValidIn_def AOT_box_def AOT_all_def AOT_equiv_def
                Lambda_denotes[simplified ValidIn_def]) blast

lemma PLM_51: \<open>[\<Turnstile>\<^sub>\<box> \<lbrace>x,F\<rbrace> \<^bold>\<rightarrow> \<^bold>\<box>\<lbrace>x,F\<rbrace>]\<close>
  by (metis AOT_box_def AOT_imp_def Enc.elims ValidNec_def)

lemma PLM_52: \<open>[\<Turnstile>\<^sub>\<box> \<lparr>O!,x\<rparr> \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<exists>F . \<lbrace>x,F\<rbrace>)]\<close>
  by (metis AOT_ex_def AOT_imp_def AOT_not_def Enc.simps(3) Ordinary_sem' ValidIn_def ValidNec_ValidIn)

lemma PLM_53: \<open>[\<Turnstile>\<^sub>\<box> \<^bold>\<exists>x . \<lparr>A!,x\<rparr> \<^bold>& (\<^bold>\<forall>F. \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<phi> F)]\<close>
proof -
  have \<open>\<exists>x. \<lparr>A!,Some x\<rparr> w \<and> (\<forall>F. \<lbrace>Some x,Some F\<rbrace> w = \<phi> (Some F) w)\<close> for w
    by (auto intro!: exI[where x=\<open>\<alpha>\<nu> {r. \<phi> (Some r) w}\<close>] simp: Abstract_sem[unfolded ValidIn_def])
  thus ?thesis
    by (simp add: AOT_ex_def AOT_conj_def AOT_equiv_def AOT_all_def ValidNec_def)
qed

section\<open>Deductive System\<close>

lemma AX: \<open>[\<Turnstile>\<^sub>\<box> \<phi>] \<Longrightarrow> [v \<Turnstile> \<phi>]\<close>
  by (simp add: ValidNec_ValidIn)

lemma MP: \<open>[v \<Turnstile> \<phi>] \<Longrightarrow> [v \<Turnstile> \<phi> \<^bold>\<rightarrow> \<psi>] \<Longrightarrow> [v \<Turnstile> \<psi>]\<close>
  by (simp add: AOT_imp_def ValidIn_def)

lemma Deduction: \<open>([v \<Turnstile> \<phi>] \<Longrightarrow> [v \<Turnstile> \<psi>]) \<Longrightarrow> [v \<Turnstile> \<phi> \<^bold>\<rightarrow> \<psi>]\<close>
  by (simp add: AOT_imp_def ValidIn_def)

lemma GEN: \<open>(\<And> x . [v \<Turnstile> \<phi> (Some x)]) \<Longrightarrow> [v \<Turnstile> \<^bold>\<forall> x . \<phi> x]\<close>
  by (simp add: AOT_all_def ValidIn_def)
lemma GEN\<o>: \<open>(\<And> p . [v \<Turnstile> \<phi> p]) \<Longrightarrow> [v \<Turnstile> \<^bold>\<forall>\<^sub>\<o> p . \<phi> p]\<close>
  using AOT_all\<^sub>\<o>_def ValidIn_def by auto

lemma RN: \<open>(\<And> v . [v \<Turnstile> \<phi>]) \<Longrightarrow> [v \<Turnstile> \<^bold>\<box>\<phi>]\<close>
  using AOT_box_def ValidIn_def by force

lemma EquivDefE1: \<open>\<phi> \<equiv>\<^sub>d\<^sub>f \<psi> \<Longrightarrow> [v \<Turnstile> \<phi> \<^bold>\<rightarrow> \<psi>]\<close>
  by (simp add: AOT_imp_def EquivDef_def ValidIn_def)

lemma EquivDefE2: \<open>\<phi> \<equiv>\<^sub>d\<^sub>f \<psi> \<Longrightarrow> [v \<Turnstile> \<psi> \<^bold>\<rightarrow> \<phi>]\<close>
  by (simp add: AOT_imp_def EquivDef_def ValidIn_def)

lemma IdDefE: \<open>\<tau> =\<^sub>d\<^sub>f \<sigma> \<Longrightarrow> [v \<Turnstile> (\<sigma>\<^bold>\<down> \<^bold>\<rightarrow> \<tau> \<^bold>= \<sigma>) \<^bold>& (\<^bold>\<not>\<sigma>\<^bold>\<down> \<^bold>\<rightarrow> \<^bold>\<not>\<tau>\<^bold>\<down>)]\<close>
  by (smt (verit, del_insts) AOT_conj_def AOT_identity_def AOT_imp_def IdDef.simps(1,2) ValidIn_def not_Some_eq)

text\<open>For a full hyperintensional implementation of second order AOT that reproduces PLM's syntax see
     @{url \<open>https://github.com/ekpyron/AOT\<close>} or @{url \<open>https://aot.ekpyron.org\<close>}.
     Note, however, that it extensively uses more advanced features of Isabelle (e.g. type classes,
     complex syntax translations implemented in ML, specialized custom outer syntax commands
     implemented in ML, etc.).\<close>

end
