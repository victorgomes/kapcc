section{* Transformer Algebras  Based on KAD *}

theory Transformer_Algebras

imports VC_KAD      

begin

no_notation inf (infixl "\<sqinter>" 70)
and sup (infixl "\<squnion>" 65)

definition bpt :: "'a :: antidomain_kleene_algebra \<Rightarrow> ('a \<Rightarrow> 'a)" ("|_\<rbrakk>") where
  "|x\<rbrakk>  = (\<lambda>p. |x] p)"

lemma bpt_box: "|x\<rbrakk>p = |x]p"
  by (simp add: bpt_def)

definition bpt_meet :: "('a :: antidomain_kleene_algebra \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 70) where 
  "f \<sqinter> g = (\<lambda>p. (f p) \<cdot> (g p))"  

definition bpt_join :: "('a :: antidomain_kleene_algebra \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 65) where 
  "f \<squnion> g = (\<lambda>p. (f p) + (g p))"                                                         

lemma bpt_seq: "|x \<cdot> y\<rbrakk> = |x\<rbrakk> \<circ> |y\<rbrakk>"
  by (intro ext, simp add: bpt_def)  

lemma bpt_add1: "|x\<rbrakk> (d p \<cdot> d q) = |x\<rbrakk> p \<cdot> |x\<rbrakk> q"
  by (simp add: fbox_add1 bpt_def) 

lemma bpt_add2: "|x + y\<rbrakk> p = |x\<rbrakk> p \<cdot> |y\<rbrakk> p" 
  by (simp add: fbox_add2 bpt_def) 

lemma bpt_add2_var: "|x + y\<rbrakk> = |x\<rbrakk> \<sqinter> |y\<rbrakk>"
  by (intro ext, simp add: bpt_meet_def bpt_add2)

lemma "|x\<rbrakk> \<squnion> |y\<rbrakk> = (\<lambda>p. |ad ( |x]p) \<cdot> y]p)"
  by (intro ext, metis (no_types, lifting) addual.ars_r_def addual.bbox_def fbox_export1 bpt_def bpt_join_def)

lemma bpt_one: "|1\<rbrakk> = (\<lambda>p. d p)"
  by (intro ext, simp add: bpt_def)

lemma bpt_zero: "|0\<rbrakk>  = (\<lambda>p. 1)"
  by (intro ext, simp add: bpt_def)
                                           
lemma bpt_mult_assoc: "( |x\<rbrakk> \<circ> |y\<rbrakk>) \<circ> |z\<rbrakk> = |x\<rbrakk> \<circ> ( |y\<rbrakk> \<circ> |z\<rbrakk>)"
  by (simp add: comp_assoc)  

lemma bpt_mult_onel: "|1\<rbrakk> \<circ> |x\<rbrakk> = |x\<rbrakk>"
  by (metis mult.left_neutral bpt_seq)

lemma bpt_mult_oner: "|x\<rbrakk> \<circ> |1\<rbrakk> = |x\<rbrakk>"
  by (metis mult.right_neutral bpt_seq)

lemma bpt_mult_annil: "|0\<rbrakk> \<circ> |x\<rbrakk> = |0\<rbrakk>"
  by (metis ds.ddual.annir bpt_seq)

lemma bpt_mult_annir: "|x\<rbrakk> \<circ> |0\<rbrakk> = |0\<rbrakk>"
  by (metis ds.ddual.annil bpt_seq)

lemma bpt_meet_assoc: "|x\<rbrakk> \<sqinter> ( |y\<rbrakk> \<sqinter> |z\<rbrakk> ) = ( |x\<rbrakk> \<sqinter> |y\<rbrakk> ) \<sqinter> |z\<rbrakk>"
  by (intro ext, simp add: bpt_meet_def ds.ddual.mult_assoc)

lemma bpt_meet_comm: "|x\<rbrakk> \<sqinter> |y\<rbrakk> = |y\<rbrakk> \<sqinter> |x\<rbrakk>"
  by (intro ext, simp add: bpt_meet_def am2 fbox_def bpt_def)

lemma bpt_meet_idem: "|x\<rbrakk> \<sqinter> |x\<rbrakk> = |x\<rbrakk>"
  by (metis dnsz.dnso1 dnsz.dsg1 bpt_add2_var)

lemma bpt_meet_zero: "|0\<rbrakk> \<sqinter> |x\<rbrakk> = |x\<rbrakk>"
  by (metis add.left_neutral bpt_add2_var)

lemma bpt_join_assoc: "|x\<rbrakk> \<squnion> ( |y\<rbrakk> \<squnion> |z\<rbrakk> ) = ( |x\<rbrakk>\<squnion> |y\<rbrakk> ) \<squnion> |z\<rbrakk>"
  by (intro ext, simp add: bpt_join_def join.sup_assoc)

lemma bpt_join_comm: "|x\<rbrakk> \<squnion> |y\<rbrakk> = |y\<rbrakk> \<squnion> |x\<rbrakk>"
  by (intro ext, simp add: bpt_join_def join.sup.commute)

lemma bpt_meet_comp_distl: "|x\<rbrakk> \<circ> |y\<rbrakk> \<sqinter> |z\<rbrakk> = ( |x\<rbrakk> \<circ> |y\<rbrakk> ) \<sqinter> ( |x\<rbrakk> \<circ> |z\<rbrakk> )"
  apply (rule ext, simp add: bpt_meet_def bpt_def)
  by (metis ds.ddual.distrib_right' fbox_add2 fbox_mult)

lemma bpt_meet_comp_distr: "( |x\<rbrakk> \<sqinter> |y\<rbrakk> ) \<circ> |z\<rbrakk> = ( |x\<rbrakk> \<circ> |z\<rbrakk> ) \<sqinter> ( |y\<rbrakk> \<circ> |z\<rbrakk> )"
  by (intro ext, simp add: bpt_meet_def bpt_def)

lemma bpt_join_meet_dist1: "|x\<rbrakk> \<sqinter> ( |y\<rbrakk> \<squnion> |z\<rbrakk> ) = ( |x\<rbrakk> \<sqinter> |y\<rbrakk> ) \<squnion> ( |x\<rbrakk> \<sqinter> |z\<rbrakk> )"
  by (intro ext, simp add: bpt_join_def bpt_meet_def)

lemma bpt_join_meet_dist2: "|x\<rbrakk> \<squnion> ( |y\<rbrakk> \<sqinter> |z\<rbrakk> ) = ( |x\<rbrakk> \<squnion> |y\<rbrakk> ) \<sqinter> ( |x\<rbrakk> \<squnion> |z\<rbrakk> )"
  apply (intro ext, simp only: bpt_meet_def bpt_join_def bpt_box)
  by (metis (no_types, lifting) addual.bbox_def fbox_add2 fbox_export1 semiring_class.distrib_left)

text {* These facts show that (backward) predicate transformers form a dioid. Can we do that by a locale statement? *}

lemma bpt_cond: "|if p then x else y fi\<rbrakk> = |d p \<cdot> x\<rbrakk> \<sqinter> |ad p \<cdot> y\<rbrakk>"
  by (intro ext, simp only: bpt_def bpt_meet_def cond_def fbox_add2)

lemma bpt_cond_var: "|if p then x else y fi\<rbrakk> = ( |d p\<rbrakk> \<circ> |x\<rbrakk> ) \<sqinter> ( |ad p\<rbrakk> \<circ> |y\<rbrakk> )"
  by (simp add: bpt_cond bpt_seq)

lemma bpt_star_unfoldl: "|1\<rbrakk> \<sqinter> ( |x\<rbrakk> \<circ> |x\<^sup>\<star>\<rbrakk> ) = |x\<^sup>\<star>\<rbrakk>"
  by (intro ext, simp add: bpt_meet_def bpt_def)

lemma bpt_star_unfoldr: "|1\<rbrakk> \<sqinter> ( |x\<^sup>\<star>\<rbrakk> \<circ> |x\<rbrakk> ) = |x\<^sup>\<star>\<rbrakk>"
  by (intro ext, simp add: bpt_meet_def bpt_def)

lemma bpt_ord_prop: "|x\<rbrakk> \<le> |y\<rbrakk> \<longleftrightarrow> |x\<rbrakk> \<sqinter> |y\<rbrakk> = |x\<rbrakk>"
  apply (simp add: bpt_def ext bpt_meet_def fbox_def le_fun_def)
  by (meson meet_ord_def)

lemma d_fbox: "|y] (p :: 'a :: antidomain_kleene_algebra) = d ( |y] p)"
  by (metis ds.ddual.mult_oner fbox_mult fbox_one)

lemma bpt_star_inductl_aux: "|y] (p :: 'a :: antidomain_kleene_algebra) \<le> |z] p \<cdot> |x]( |y] p) \<Longrightarrow> |y] p \<le> |x\<^sup>\<star>]( |z] p)"
  by (metis d_fbox fbox_star_induct)

lemma bpt_star_intuctl: "|y\<rbrakk> \<le> |z\<rbrakk> \<sqinter> ( |x\<rbrakk> \<circ> |y\<rbrakk>) \<Longrightarrow> |y\<rbrakk> \<le> |x\<^sup>\<star>\<rbrakk> \<circ> |z\<rbrakk>"
  by (simp add: bpt_meet_def bpt_def bpt_star_inductl_aux le_fun_def)

text {* We can also define a specification statement at this level. We need to prove that this gives us the correct
 thing by a correspondence proof with the lower level. *}

definition aH :: "('a :: ord \<Rightarrow> 'a ) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "aH f g h \<longleftrightarrow> f \<le> g \<circ> h"

lemma spec_lift: "|d p\<rbrakk> \<le> |x\<rbrakk> \<circ> |d q\<rbrakk> \<Longrightarrow> ad p \<le> |x] (ad q)"
proof -
  assume "|d p\<rbrakk> \<le> |x\<rbrakk> \<circ> |d q\<rbrakk>"
  hence "\<forall>y. |d p] y \<le> |x]|d q]y"
    by (metis bpt_def bpt_seq fbox_seq le_funD)
  hence "|d p] 0 \<le> |x]|d q] 0"
    by blast
  thus "ad p \<le> |x] (ad q)"
    by (metis (no_types, lifting) addual.ars_r_def addual.bbox_def am3 apd2 dpdz.domain_invol dual_order.trans fbox_dom)
qed

lemma "rdom X \<subseteq> rdom Y \<Longrightarrow> (\<forall>Z. rdom (X ; Z) \<subseteq> rdom (Y ; Z))" 
apply (simp add: rel_antidomain_kleene_algebra.ads_d_def rel_ad_def)
nitpick
oops

lemma "rel_ad p \<le> wp x (rel_ad q) \<Longrightarrow> (\<forall>y. wp (rdom p) y \<le> wp x (wp (rdom q) y))"
nitpick
oops

lemma (in antidomain_semiring) "d x \<le> d y \<Longrightarrow> (\<forall>z. d (x \<cdot> z) \<le> d (y \<cdot> z))"
nitpick

end

lemma (in antidomain_semiring)
assumes "(\<forall>p. |x]p \<le> |y]p) \<Longrightarrow> y \<le> x"
shows "ad p \<le> |x] (ad q) \<Longrightarrow> (\<forall>y. |d p]y \<le> |x] |d q]y)"


text {* If we can encode the effect of an assignment at the level of the algebra, we might get a way of doing program verification
and refinement purely symbolically, at least for straight line programs. This would require us to link assignments with substitutions. *}

text {* This shows that the transformer algebra forms a left Kleene algebra. Again: can we do a locale proof? *}

interpretation left_kleene_algebra "\<lambda>x y. (pt_meet |x\<rbrakk> |y\<rbrakk>) 1" "\<lambda>x y. ( |x\<rbrakk> \<circ> |y\<rbrakk>) 1"
apply standard
prefer 8
apply (simp add: bpt_meet_def bpt_def)
oops

interpretation left_kleene_algebra tp "op \<circ>" "op \<le>" "op <" "|1\<rbrakk>" "\<lambda>f. f"
apply standard
prefer 8
(* nitpick *)
oops

text {* We get dual results for the backward boxes. *}

end
