section {* Domain Quantales *}

theory Domain_Quantale
  imports "$AFP/KAD/Modal_Kleene_Algebra"
begin

subsection {* Notation *}

notation
  times (infixl "\<cdot>" 70)
  
notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf (infixl "\<sqinter>" 65) and
  sup (infixl "\<squnion>" 65) and
  Inf ("\<Sqinter>_" [900] 900) and
  Sup ("\<Squnion>_" [900] 900)

syntax
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)

subsection {* Definitions of Lattice-Ordered Monoids with Domain*}

class bd_lattice_ordered_monoid = bounded_lattice + distrib_lattice + monoid_mult +
  assumes left_distrib: "x \<cdot> (y \<squnion> z) = x \<cdot> y \<squnion> x \<cdot> z"
  and right_distrib: "(x \<squnion> y) \<cdot> z = x \<cdot> z \<squnion> y \<cdot> z"
  and bot_annil [simp]: "\<bottom> \<cdot> x = \<bottom>"
  and bot_annir [simp]: "x \<cdot> \<bottom> = \<bottom>"
begin

sublocale semiring_one_zero "op \<squnion>" "op \<cdot>" "1" "bot" 
  by (standard, auto simp: sup.assoc sup.commute sup_left_commute left_distrib right_distrib sup_absorb1)   
  
sublocale dioid_one_zero "op \<squnion>" "op \<cdot>" "1" bot "op \<le>" "op <"
  by (standard, simp add: local.le_iff_sup, auto)

end

no_notation ads_d ("d")
  and ars_r ("r")
  and antirange_op ("ar _" [999] 1000)

class domain_bdlo_monoid = bd_lattice_ordered_monoid +
  assumes rdv: "(z \<sqinter> x \<cdot> top) \<cdot> y = z \<cdot> y \<sqinter> x \<cdot> top"  

begin 

definition "d x = 1 \<sqinter> x \<cdot> \<top>"

sublocale ds: domain_semiring "op \<squnion>" "op \<cdot>" "1" "\<bottom>" "d" "op \<le>" "op <"
proof standard
  fix x y
  show "x \<squnion> d x \<cdot> x = d x \<cdot> x"
    by (metis d_def local.inf_sup_absorb local.left_distrib local.mult_1_left local.mult_1_right local.rdv local.sup.absorb_iff1 local.sup.idem local.sup.left_commute top_greatest)
  show "d (x \<cdot> d y) = d (x \<cdot> y)"
    by (simp add: d_def local.inf_absorb2 local.rdv  mult_assoc)
  show "d x \<squnion> 1 = 1"
    by (simp add: d_def local.sup.commute)
  show "d bot = bot"
    by (simp add: d_def local.inf.absorb1 local.inf.commute)
  show "d (x \<squnion> y) = d x \<squnion> d y"
    by (simp add: d_def local.inf_sup_distrib1)
qed

end

class boolean_monoid = boolean_algebra + monoid_mult +  
assumes left_distrib': "x \<cdot> (y \<squnion> z) = x \<cdot> y \<squnion> x \<cdot> z"
and right_distrib': "(x \<squnion> y) \<cdot> z = x \<cdot> z \<squnion> y \<cdot> z"
and bot_annil' [simp]: "\<bottom> \<cdot> x = \<bottom>"
and bot_annir' [simp]: "x \<cdot> \<bottom> = \<bottom>"

begin

subclass bd_lattice_ordered_monoid
  by (standard, simp_all add: local.left_distrib' local.right_distrib')

lemma inf_bot_iff_le: "x \<sqinter> y = \<bottom> \<longleftrightarrow> x \<le> -y"
  by (metis le_iff_inf inf_sup_distrib1 inf_top_right sup_bot.left_neutral sup_compl_top compl_inf_bot inf.assoc inf_bot_right)

end

class domain_boolean_monoid = boolean_monoid + 
  assumes rdv': "(z \<sqinter> x \<cdot> \<top>) \<cdot> y = z \<cdot> y \<sqinter> x \<cdot> \<top>"     

begin

sublocale dblo: domain_bdlo_monoid "1" "op \<cdot>" "op \<sqinter>" "op \<le>" "op <" "op \<squnion>" "\<bottom>" "\<top>"
  by (standard, simp add: local.rdv')

definition "a x = 1 \<sqinter> -(dblo.d x)"
                                
lemma a_d_iff: "a x = 1 \<sqinter> -(x \<cdot> \<top>)"
  by (auto simp: a_def dblo.d_def inf_sup_distrib1) 

lemma topr: "-(x \<cdot> \<top>) \<cdot> \<top> = -(x \<cdot> \<top>)" 
proof (rule antisym)
  show "-(x \<cdot> \<top>) \<le> -(x \<cdot> \<top>) \<cdot> \<top>"
    by (metis local.mult_isol_var local.mult_oner local.order_refl local.top_greatest)
  have "-(x \<cdot> \<top>) \<sqinter> (x \<cdot> \<top>) = \<bottom>"
    by simp
  hence "(-(x \<cdot> \<top>) \<sqinter> (x \<cdot> \<top>)) \<cdot> \<top>  = \<bottom>"
    by simp 
  hence "-(x \<cdot> \<top>) \<cdot> \<top> \<sqinter> (x \<cdot> \<top>)  = \<bottom>"
    by (metis local.rdv') 
  thus "-(x \<cdot> \<top>) \<cdot> \<top> \<le> -(x \<cdot> \<top>)"
    by (simp add: local.inf_bot_iff_le)
qed

lemma dd_a: "dblo.d x = a (a x)"
  by (metis a_d_iff dblo.d_def local.double_compl local.inf_top.left_neutral local.mult_1_left local.rdv' topr)

lemma ad_a [simp]: "a (dblo.d x) = a x"
  by (simp add: a_def)

lemma da_a [simp]: "dblo.d (a x) = a x"
  using ad_a dd_a by auto

lemma a1 [simp]: "a x \<cdot> x = \<bottom>"
proof -
  have "a x \<cdot> x \<cdot> \<top> = \<bottom>"
    by (metis a_d_iff local.inf_compl_bot local.mult_1_left local.rdv' topr)
  then show ?thesis
    by (metis (no_types) dblo.d_def dblo.ds.domain_very_strict local.inf_bot_right)
qed

lemma a2 [simp]: "a (x \<cdot> y) \<squnion> a (x \<cdot> a (a y)) = a (x \<cdot> a (a y))"
  by (metis a_def dblo.ds.dsr2 dd_a local.sup.idem)

lemma a3 [simp]: "a (a x) \<squnion> a x = 1"
  by (metis a_def da_a local.inf.commute local.sup.commute local.sup_compl_top local.sup_inf_absorb local.sup_inf_distrib1)

subclass domain_bdlo_monoid ..

sublocale ad: antidomain_semiring a "op \<squnion>" "op \<cdot>" "1" "\<bottom>" "op \<le>" "op <"
  rewrites ad_eq: "ad.ads_d x = d x"
proof -
  show "class.antidomain_semiring a op \<squnion> op \<cdot> 1 \<bottom> op \<le> op <"
    by (standard, simp_all)
  then interpret ad: antidomain_semiring a "op \<squnion>" "op \<cdot>" "1" "\<bottom>" "op \<le>" "op <" .
  show "ad.ads_d x = d x"
    by (simp add: ad.ads_d_def dd_a)
qed

end 


class range_boolean_monoid = boolean_monoid + 
  assumes ldv': "y \<cdot> (z \<sqinter> \<top> \<cdot> x) = y \<cdot> z \<sqinter> \<top> \<cdot> x"
begin

definition "r x = 1 \<sqinter> \<top> \<cdot> x"

definition "ar x = 1 \<sqinter> -(r x)"
                                
lemma ar_r_iff: "ar x = 1 \<sqinter> -(\<top> \<cdot> x)"
  by (simp add: ar_def local.inf_sup_distrib1 r_def)

lemma topl: "\<top>\<cdot>(-(\<top> \<cdot> x)) = -(\<top> \<cdot> x)" 
proof (rule antisym)
  show "\<top> \<cdot> - (\<top> \<cdot> x) \<le> - (\<top> \<cdot> x)"
    by (metis local.bot_annir' local.compl_inf_bot local.inf_bot_iff_le local.ldv')
  show "- (\<top> \<cdot> x) \<le> \<top> \<cdot> - (\<top> \<cdot> x)"
    by (metis local.inf_le2 local.inf_top.right_neutral local.mult_1_left local.mult_isor)
qed

lemma r_ar: "r x = ar (ar x)"
  by (metis ar_r_iff local.double_compl local.inf.commute local.inf_top.right_neutral local.ldv' local.mult_1_right r_def topl)

lemma ar_ar [simp]: "ar (r x) = ar x"
  by (simp add: ar_def local.ldv' r_def)

lemma rar_ar [simp]: "r (ar x) = ar x"
  using r_ar ar_ar by auto

lemma ar1 [simp]: "x \<cdot> ar x = \<bottom>"
proof -
  have "\<top> \<cdot> x \<cdot> ar x = \<bottom>"
    by (metis ar_r_iff local.inf_compl_bot local.ldv' local.mult_oner topl)
  then show ?thesis
    by (metis ar_r_iff local.double_compl local.inf_bot_iff_le local.inf_le2 local.inf_top.right_neutral local.ldv' local.mult_1_left local.mult_isor local.mult_oner topl)
qed

lemma ars: "r (r x \<cdot> y) = r (x \<cdot> y)"
  by (metis local.inf.commute local.inf_top.right_neutral local.ldv' local.mult_oner mult_assoc r_def)

lemma ar2 [simp]: "ar (x \<cdot> y) \<squnion> ar (ar (ar x) \<cdot> y) = ar (ar (ar x) \<cdot> y)"
  by (metis ar_def ars r_ar local.sup.idem)
                         
lemma ar3 [simp]: "ar (ar x) \<squnion> ar x = 1 "
  by (metis ar_def rar_ar local.inf.commute local.sup.commute local.sup_compl_top local.sup_inf_absorb local.sup_inf_distrib1)

sublocale ar: antirange_semiring "op \<squnion>" "op \<cdot>" "1" "\<bottom>" ar "op \<le>" "op <"
  rewrites ar_eq: "ar.ars_r x = r x"
proof -
  show "class.antirange_semiring op \<squnion> op \<cdot> 1 \<bottom> ar op \<le> op <"
    by (standard, simp_all)
  then interpret ar: antirange_semiring "op \<squnion>" "op \<cdot>" "1" "\<bottom>" ar "op \<le>" "op <" .
  show "ar.ars_r x = r x"
    by (simp add: ar.ars_r_def r_ar)
qed

end

subsection {* Definition of Quantale *}

class quantale = complete_lattice + monoid_mult +
  assumes Sup_distr: "\<Squnion> X \<cdot> y = \<Squnion> {z. \<exists>x \<in> X. z = x \<cdot> y}"
  and Sup_distl: "x \<cdot> \<Squnion> Y = \<Squnion> {z. \<exists>y \<in> Y. z = x \<cdot> y}"       

begin

lemma bot_annil'' [simp]: "\<bottom> \<cdot> x = \<bottom>"
  using Sup_distr[where X="{}"] by auto

lemma bot_annirr'' [simp]: "x \<cdot> \<bottom> = \<bottom>"
  using Sup_distl[where Y="{}"] by auto

lemma sup_distl: "x \<cdot> (y \<squnion> z) = x \<cdot> y \<squnion> x \<cdot> z"
  using Sup_distl[where Y="{y, z}"] by (fastforce intro!: Sup_eqI)

lemma sup_distr: "(x \<squnion> y) \<cdot> z = x \<cdot> z \<squnion> y \<cdot> z"
  using Sup_distr[where X="{x, y}"] by (fastforce intro!: Sup_eqI)

sublocale semiring_one_zero "op \<squnion>" "op \<cdot>" "1" "\<bottom>" 
  by (standard, auto simp: sup.assoc sup.commute sup_left_commute sup_distl sup_distr)     

sublocale dioid_one_zero "op \<squnion>" "op \<cdot>" "1" "\<bottom>" "op \<le>" "op <"
  by (standard, simp add: local.le_iff_sup, auto)

lemma Sup_sup_pred: "x \<squnion> \<Squnion>{y. P y} = \<Squnion>{y. y = x \<or> P y}"
  apply (rule antisym)
  apply (simp add: Collect_mono local.Sup_subset_mono local.Sup_upper) 
  using local.Sup_least local.Sup_upper local.le_supI2 by fastforce

definition star :: "'a \<Rightarrow> 'a" where
  "star x = (\<Squnion>i. x ^ i)"

lemma star_def_var1: "star x = \<Squnion>{y. \<exists>i. y = x ^ i}"
  by (simp add: star_def full_SetCompr_eq)

lemma star_def_var2: "star x = \<Squnion>{x ^ i |i. True}"
  by (simp add: star_def full_SetCompr_eq)

lemma star_unfoldl' [simp]: "1 \<squnion> x \<cdot> (star x) = star x"
proof -
  have "1 \<squnion> x \<cdot> (star x) = x ^ 0 \<squnion> x \<cdot> \<Squnion>{y. \<exists>i. y = x ^ i}"
    by (simp add: star_def_var1)
  also have "... = x ^ 0 \<squnion> \<Squnion>{y. \<exists>i. y = x ^ (i + 1)}"
    by (simp add: Sup_distl, metis)
  also have "... = \<Squnion>{y. y = x ^ 0 \<or> (\<exists>i. y = x ^ (i + 1))}"
    using Sup_sup_pred by auto
  also have "... = \<Squnion>{y. \<exists>i. y = x ^ i}"
    by (metis Suc_eq_plus1 power.power.power_Suc power.power_eq_if)
  finally show ?thesis
    by (simp add: star_def_var1)
qed

lemma star_unfoldr' [simp]: "1 \<squnion> (star x) \<cdot> x = star x"
proof -
  have "1 \<squnion> (star x) \<cdot> x = x ^ 0 \<squnion> \<Squnion>{y. \<exists>i. y = x ^ i} \<cdot> x"
    by (simp add: star_def_var1)
  also have "... = x ^ 0 \<squnion> \<Squnion>{y. \<exists>i. y = x ^ i \<cdot> x}"
    by (simp add: Sup_distr, metis)
  also have "... = x ^ 0 \<squnion> \<Squnion>{y. \<exists>i. y = x ^ (i + 1)}"
    using local.power_Suc2 by auto  
   also have "... = \<Squnion>{y. y = x ^ 0 \<or> (\<exists>i. y = x ^ (i + 1))}"
    using Sup_sup_pred by auto
  also have "... = \<Squnion>{y. \<exists>i. y = x ^ i}"
    by (metis Suc_eq_plus1 power.power.power_Suc power.power_eq_if)
  finally show ?thesis
    by (simp add: star_def_var1)
qed

lemma (in dioid_one_zero) power_inductl: "z + x \<cdot> y \<le> y \<Longrightarrow> (x ^ n) \<cdot> z \<le> y"
proof (induct n)
  case 0 show ?case
    using "0.prems" by auto
  case Suc thus ?case
    by (auto, metis mult.assoc mult_isol order_trans)
qed

lemma (in dioid_one_zero) power_inductr: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> (x ^ n) \<le> y"
proof (induct n)
  case 0 show ?case
    using "0.prems" by auto
  case Suc
  {
    fix n
    assume "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x ^ n \<le> y"
      and "z + y \<cdot> x \<le> y"
    hence "z \<cdot> x ^ n \<le> y"
      by auto
    also have "z \<cdot> x ^ Suc n = z \<cdot> x \<cdot> x ^ n"
      by (metis mult.assoc power_Suc)
    moreover have "... = (z \<cdot> x ^ n) \<cdot> x"
      by (metis mult.assoc power_commutes)
    moreover have "... \<le> y \<cdot> x"
      by (metis calculation(1) mult_isor)
    moreover have "... \<le> y"
      using `z + y \<cdot> x \<le> y` by auto
    ultimately have "z \<cdot> x ^ Suc n \<le> y" by auto
  }
  thus ?case
    by (metis Suc)
qed

lemma star_inductl': "z \<squnion> x \<cdot> y \<le> y \<Longrightarrow> (star x) \<cdot> z \<le> y" 
proof -
  assume "z \<squnion> x \<cdot> y \<le> y"
  hence "\<forall>i. x ^ i \<cdot> z \<le> y"
    by (simp add: local.power_inductl)
  hence "\<Squnion>{w. \<exists>i. w = x ^ i \<cdot> z} \<le> y"
    by (intro Sup_least, auto)
  hence "\<Squnion>{w. \<exists>i. w = x ^ i} \<cdot> z \<le> y"
    using local.Sup_distr local.Sup_le_iff by auto
  thus "(star x) \<cdot> z \<le> y"
    by (simp add: local.star_def_var1)
qed

lemma star_inductr': "z \<squnion> y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> (star x) \<le> y" 
proof -
  assume "z \<squnion> y \<cdot> x \<le> y"
  hence "\<forall>i. z \<cdot> x ^ i  \<le> y"
    by (simp add: local.power_inductr)
  hence "\<Squnion>{w. \<exists>i. w = z \<cdot> x ^ i} \<le> y"
    by (intro Sup_least, auto)
  hence "z \<cdot> \<Squnion>{w. \<exists>i. w = x ^ i} \<le> y"
    using local.Sup_distl local.Sup_le_iff by auto
  thus "z \<cdot> (star x) \<le> y"
    by (simp add: local.star_def_var1)
qed

sublocale ka: kleene_algebra "op \<squnion>" "op \<cdot>" "1" "\<bottom>" "op \<le>" "op <" star
  by standard (simp_all add: star_inductl' local.star_inductr')

end

class distributive_quantale = quantale + distrib_lattice (* this is probably not true as we need infinite distributivity laws ! *)

begin

subclass bd_lattice_ordered_monoid
  by (standard, simp_all add: local.distrib_left)

lemma "(1 \<sqinter> x \<cdot> \<top>) \<cdot> x = x"
nitpick
oops

end 

subsection {* Domain Quantales *}

class domain_quantale = distributive_quantale +
  assumes rdv'': "(z \<sqinter> x \<cdot> \<top>) \<cdot> y = z \<cdot> y \<sqinter> x \<cdot> \<top>"  

begin

subclass domain_bdlo_monoid 
  by (standard, simp add: local.rdv'')

end

class range_quantale = distributive_quantale +
  assumes ldv'': "y \<cdot> (z \<sqinter> \<top> \<cdot> x) = y \<cdot> z \<sqinter> \<top> \<cdot> x"

class boolean_quantale = quantale + complete_boolean_algebra

begin

subclass boolean_monoid
  by (standard, simp_all add: local.sup_distl)

lemma "(1 \<sqinter> x \<cdot> \<top>) \<cdot> x = x"
nitpick
oops

lemma "(1 \<sqinter> -(x \<cdot> \<top>)) \<cdot> x = \<bottom>"
nitpick
oops

end

class domain_boolean_quantale = domain_quantale + boolean_quantale

begin

subclass domain_boolean_monoid
  by (standard, simp add: local.rdv'')

lemma fbox_eq: "ad.fbox x q = Sup{d(p)| p. d(p)*x \<le> x*d(q)}"
  apply (rule Sup_eqI[symmetric])
  apply clarsimp
  using local.ad.fbox_demodalisation3 local.ad.fbox_simp apply auto[1]
  apply clarsimp
  by (metis local.ad.fbox_def local.ad.fbox_demodalisation3 local.ad.fbox_simp local.da_a local.eq_refl)

lemma fdia_eq: "ad.fdia x p = Inf{d(q)|q. x*d(p) \<le> d(q)*x}"
  apply (rule Inf_eqI[symmetric])
  apply clarsimp
  using local.ds.fdemodalisation2 apply auto[1]
  apply clarsimp
  by (metis local.ad.fd_eq_fdia local.ad.fdia_def local.da_a local.double_compl local.ds.fdemodalisation2 local.inf_bot_iff_le local.inf_compl_bot)

(* proof of axioms for RKAT -- H p x q \<longleftrightarrow> p \<le> fbox x q *)
definition R :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "R p q \<equiv> Sup{x. d(p)*x \<le> x*d(q)}"

lemma "x \<le> R p q \<Longrightarrow> d(p) \<le> ad.fbox x (d q)"
proof (simp add: R_def ad.kat_1_equiv ad.kat_2_equiv)
  assume "x \<le> \<Squnion>{x. d p \<cdot> x \<cdot> a q = \<bottom>}"
  hence "d p \<cdot> x \<cdot> a q \<le> d p \<cdot> \<Squnion>{x. d p \<cdot> x \<cdot> a q = \<bottom>} \<cdot> a q "
    using local.mult_double_iso by blast
  also have "... = \<Squnion>{d p \<cdot> x \<cdot> a q | x. d p \<cdot> x \<cdot> a q = \<bottom>}"
    apply (subst Sup_distl)
    apply (subst Sup_distr)
    apply clarsimp
    apply metis
  done
  also have "... = \<bottom>"
    by (auto simp: Sup_eqI)
  finally show ?thesis
    using ad.fbox_demodalisation3 local.ad.kat_3 local.ad.kat_4 local.le_bot by blast
qed

lemma "d(p) \<le> ad.fbox x (d q) \<Longrightarrow> x \<le> R p q"
  apply (simp add: R_def)
  apply (rule Sup_upper)
  apply simp
  using local.ad.fbox_demodalisation3 local.ad.fbox_simp apply auto[1]
done

end

interpretation rel_dbq: domain_boolean_quantale Inter Union "op \<inter>" "op \<subseteq>" "op \<subset>" "op \<union>" "{}" UNIV minus uminus Id "op O"
  apply (standard, simp_all add: O_assoc)
  by blast +

class range_boolean_quantale = range_quantale + boolean_quantale

begin

subclass range_boolean_monoid
  by (standard, simp add: local.ldv'')

lemma fbox_eq: "ar.bbox x (r q) = Sup{r(p)| p. x*r(p) \<le> r(q)*x}"
  apply (rule Sup_eqI[symmetric])
  apply clarsimp
  using ar.ardual.fbox_demodalisation3 local.ar.ardual.fbox_simp apply auto[1]
  apply clarsimp
  by (metis local.ar.ardual.fbox_def local.ar.ardual.fbox_demodalisation3 local.eq_refl local.rar_ar)

lemma fdia_eq: "ar.bdia x (r p) = Inf{r(q)|q. r(p)*x \<le> x*r(q)}"
  apply (rule Inf_eqI[symmetric])
  apply clarsimp
  using ar.ars_r_def local.ar.ardual.fdemodalisation22 local.ar.ardual.kat_3_equiv_opp local.ar.ardual.kat_4_equiv_opp apply auto[1]
  apply clarsimp
  using ar.bdia_def local.ar.ardual.ds.fdemodalisation2 local.r_ar by fastforce

end

class modal_boolean_quantale = domain_boolean_quantale + range_boolean_quantale +
  assumes domrange' [simp]: "d (r x) = r x"
  and rangedom' [simp]: "r (d x) = d x"
begin

sublocale mka: modal_kleene_algebra "op \<squnion>" "op \<cdot>" 1 \<bottom> "op \<le>" "op <" star a ar
  by standard (simp_all add: ar_eq ad_eq)

end

no_notation fbox ("( |_] _)" [61,81] 82)
  and antidomain_semiringl_class.fbox ("( |_] _)" [61,81] 82)
notation ad.fbox ("( |_] _)" [61,81] 82)

lemma recursion: "mono (f :: 'a \<Rightarrow> 'a :: domain_boolean_quantale) \<Longrightarrow> 
  (\<And>x. d p \<le> |x] d q \<Longrightarrow> d p \<le> |f x] d q) \<Longrightarrow>  d p \<le> |lfp f] d q"
  apply (erule lfp_ordinal_induct [where f=f], simp)
  apply (auto simp: ad.addual.ardual.fbox_demodalisation3 Sup_distr Sup_distl intro: Sup_mono)
done


end