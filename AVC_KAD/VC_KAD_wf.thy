section{* Verification Component Based on KAD *}

theory VC_KAD_wf

imports VC_KAD "$AFP/KAD//Modal_Kleene_Algebra_Applications"

begin

subsection {* Relational Model of Divergence Kleene Algebras *}

definition rel_nabla :: "'a rel \<Rightarrow> 'a rel" where 
  "rel_nabla X = \<Union> {P. P \<subseteq> relfdia X P}"

definition rel_nabla_bin :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where 
  "rel_nabla_bin X Q = \<Union> {P. P \<subseteq> relfdia X P \<union> rdom Q}"

lemma rel_nabla_d_closed [simp]:  "rdom (rel_nabla x) = rel_nabla x"
  by (auto simp: rel_nabla_def rel_antidomain_kleene_algebra.fdia_def rel_antidomain_kleene_algebra.ads_d_def rel_ad_def)

lemma rel_nabla_bin_d_closed [simp]:  "rdom (rel_nabla_bin x q) = rel_nabla_bin x q"
  by (auto simp: rel_nabla_bin_def rel_antidomain_kleene_algebra.fdia_def rel_antidomain_kleene_algebra.ads_d_def rel_ad_def)

lemma rel_nabla_unfold: "rel_nabla X \<subseteq> relfdia X (rel_nabla X)"
  by (simp add: rel_nabla_def rel_ad_def rel_antidomain_kleene_algebra.fdia_def, blast)

lemma rel_nabla_bin_unfold: "rel_nabla_bin X Q \<subseteq> relfdia X (rel_nabla_bin X Q) \<union> rdom Q"
  by (simp add: rel_nabla_bin_def rel_ad_def rel_antidomain_kleene_algebra.fdia_def, blast)

lemma rel_nabla_coinduct_var: "P \<subseteq> relfdia X P \<Longrightarrow> P \<subseteq> rel_nabla X"
  by (simp add: rel_nabla_def rel_antidomain_kleene_algebra.fdia_def rel_ad_def, blast)

lemma rel_nabla_bin_coinduct: "P \<subseteq> relfdia X P \<union> rdom Q \<Longrightarrow> P \<subseteq> rel_nabla_bin X Q"
  by (simp add: rel_nabla_bin_def rel_antidomain_kleene_algebra.fdia_def rel_ad_def, blast)

text {* The two fusion lemmas are, in fact, hard-coded fixpoint fusion proofs. They might be replaced
by more generic fusion proofs eventually. *}

lemma nabla_fusion1: "rel_nabla X \<union> relfdia (X\<^sup>*) Q \<subseteq> rel_nabla_bin X Q"  
proof -
  have "rel_nabla X \<union> relfdia (X\<^sup>*) Q \<subseteq> relfdia X (rel_nabla X) \<union> relfdia X (relfdia (X\<^sup>*) Q) \<union> rdom Q"
    by (metis (no_types, lifting) Un_mono inf_sup_aci(6) order_refl rel_antidomain_kleene_algebra.dka.fdia_star_unfold_var rel_nabla_unfold sup.commute)
  also have "... = relfdia X (rel_nabla X \<union> relfdia (X\<^sup>*) Q) \<union> rdom Q"
    by (simp add: rel_antidomain_kleene_algebra.dka.fdia_add1)
  finally show ?thesis
    using rel_nabla_bin_coinduct by blast
qed

lemma rel_ad_inter_seq: "rel_ad X \<inter> rel_ad Y = rel_ad X ; rel_ad Y"
  by (auto simp: rel_ad_def)

lemma fusion2_aux2: "rdom (rel_nabla_bin X Q) \<subseteq> rdom (rel_nabla_bin X Q \<inter> rel_ad (relfdia (X\<^sup>*) Q) \<union> relfdia (X\<^sup>*) Q)"
  apply (auto simp: rel_antidomain_kleene_algebra.ads_d_def rel_ad_def)
  by (metis pair_in_Id_conv r_into_rtrancl rel_antidomain_kleene_algebra.a_one rel_antidomain_kleene_algebra.a_star rel_antidomain_kleene_algebra.addual.ars_r_def rel_antidomain_kleene_algebra.dka.dns1'' rel_antidomain_kleene_algebra.dpdz.dom_one rel_antidomain_kleene_algebra.ds.ddual.rsr5 rel_antidomain_kleene_algebra.dual.conway.dagger_unfoldr_eq rel_antidomain_kleene_algebra.dual.tc_eq rel_nabla_bin_d_closed)  

lemma nabla_fusion2: "rel_nabla_bin X Q \<subseteq> rel_nabla X \<union> relfdia (X\<^sup>*) Q"
proof -
  have "rel_nabla_bin X Q \<inter> rel_ad (relfdia (X\<^sup>*) Q)  \<subseteq> (relfdia X (rel_nabla_bin X Q) \<union> rdom Q) \<inter> rel_ad (relfdia (X\<^sup>*) Q)"
    by (meson Int_mono equalityD1 rel_nabla_bin_unfold)
  also have "... \<subseteq> (relfdia X (rel_nabla_bin X Q \<inter> rel_ad (relfdia (X\<^sup>*) Q) \<union> relfdia (X\<^sup>*) Q) \<union> rdom Q) \<inter> rel_ad (relfdia (X\<^sup>*) Q)"  
    using fusion2_aux2 rel_antidomain_kleene_algebra.dka.fd_iso1 by blast
  also have "... = (relfdia X (rel_nabla_bin X Q \<inter> rel_ad (relfdia (X\<^sup>*) Q)) \<union> relfdia X (relfdia (X\<^sup>*) Q) \<union> rdom Q) \<inter> rel_ad (relfdia (X\<^sup>*) Q)"
    by (simp add: rel_antidomain_kleene_algebra.dka.fdia_add1)
  also have "... = (relfdia X (rel_nabla_bin X Q \<inter> rel_ad (relfdia (X\<^sup>*) Q)) \<union> relfdia (X\<^sup>*) Q) \<inter> rel_ad (relfdia (X\<^sup>*) Q)"
    using rel_antidomain_kleene_algebra.dka.fdia_star_unfold_var by blast
  finally have "rel_nabla_bin X Q \<inter> rel_ad (relfdia (X\<^sup>*) Q) \<subseteq> relfdia X ((rel_nabla_bin X Q) \<inter> rel_ad (relfdia (X\<^sup>*) Q))"
    by (metis (no_types, lifting) inf_commute order_trans_rules(23) rel_ad_inter_seq rel_antidomain_kleene_algebra.a_mult_add rel_antidomain_kleene_algebra.a_subid_aux1' rel_antidomain_kleene_algebra.addual.bdia_def rel_antidomain_kleene_algebra.ds.ddual.rsr5)
  hence "rdom (rel_nabla_bin X Q) ; rel_ad (relfdia (X\<^sup>*) Q) \<subseteq> rdom (rel_nabla X)"
    by (metis rel_ad_inter_seq rel_antidomain_kleene_algebra.addual.ars_r_def rel_nabla_bin_d_closed rel_nabla_coinduct_var rel_nabla_d_closed)
  thus ?thesis
    by (metis rel_antidomain_kleene_algebra.addual.ars_r_def rel_antidomain_kleene_algebra.addual.bdia_def rel_antidomain_kleene_algebra.d_a_galois1 rel_antidomain_kleene_algebra.dpdz.domain_invol rel_nabla_bin_d_closed rel_nabla_d_closed)
qed

lemma rel_nabla_coinduct: "P \<subseteq> relfdia X P \<union> rdom Q \<Longrightarrow> P \<subseteq> rel_nabla X \<union> relfdia (rtrancl X) Q"
  by (meson nabla_fusion2 order_trans rel_nabla_bin_coinduct)

interpretation rel_fdivka: fdivergence_kleene_algebra rel_ad "op \<union>" "op ; " Id "{}" "op \<subseteq>" "op \<subset>" rtrancl rel_nabla
proof 
  fix x y z:: "'a rel"
  show "rdom (rel_nabla x) = rel_nabla x"
    by simp
  show "rel_nabla x \<subseteq> relfdia x (rel_nabla x)"
    by (simp add: rel_nabla_unfold)
  show "rdom y \<subseteq> relfdia x y \<union> rdom z \<Longrightarrow> rdom y \<subseteq> rel_nabla x \<union> relfdia (x\<^sup>*) z"
    by (simp add: rel_nabla_coinduct)
qed

subsection {* A Loop Verification Rule *}

context fdivergence_kleene_algebra
begin

text {* The rule is inspired by Arden' rule from language theory. *}

lemma fdia_arden: "\<nabla>x = 0 \<Longrightarrow> d p \<le> d q + |x\<rangle> p \<Longrightarrow> d p \<le> |x\<^sup>\<star>\<rangle> q"
proof -
  assume a1: "\<nabla>x = zero_class.zero"
  assume "d p \<le> d q + |x\<rangle> p"
  then have "ad (ad p) \<le> zero_class.zero + ad (ad (x\<^sup>\<star> \<cdot> q))"
    using a1 add_commute ads_d_def dka.fd_def nabla_coinduction by force
  then show ?thesis
    by (simp add: ads_d_def dka.fd_def)
qed

lemma fdia_arden_eq: "\<nabla>x = 0 \<Longrightarrow> d p = d q + |x\<rangle> p \<Longrightarrow> d p = |x\<^sup>\<star>\<rangle> q"
  by (simp add: fdia_arden dka.fdia_star_induct_eq eq_iff)

lemma fdia_arden_iff: "\<nabla>x = 0 \<Longrightarrow> (d p = d q + |x\<rangle> p \<longleftrightarrow> d p = |x\<^sup>\<star>\<rangle> q)"
  by (metis fdia_arden_eq dka.fdia_d_simp dka.fdia_star_unfold_var)

lemma fbox_ind: "d p \<le> d q \<cdot> |x] p \<Longrightarrow> d p \<le> |x\<^sup>\<star>] q"   
proof -
assume h0: "d p \<le> d q \<cdot> |x] p"
hence h1: "d p \<le> d q" and h2: "d p \<le> |x] p"
apply (metis a_subid_aux2 dual_order.trans fbox_def)
using h0 dka.dom_subid_aux2 dual_order.trans by blast
hence "|x\<rangle> ad p \<le> ad p"
by (metis a_2_var addual.bbox_def ads_d_def dka.dsg4 ds.fd_def)
hence "|x\<^sup>\<star>\<rangle> ad p \<le> ad p"
by (smt a_2_var a_antitone' a_gla2 ads_d_def dka.fdia_star_induct_var fdia_def)
hence "d p \<le> |x\<^sup>\<star>] p"
by (simp add: h2 fbox_star_induct_var)
thus ?thesis
using h0 fbox_star_induct by blast
qed

lemma  "|x\<^sup>\<star>] p \<le> |x] p"
  by (simp add: fbox_antitone_var)

lemma fbox_arden:  "\<nabla>x = 0 \<Longrightarrow> d q \<cdot> |x] p \<le> d p \<Longrightarrow> |x\<^sup>\<star>] q \<le> d p"
proof -
assume h1: "\<nabla>x = 0" and "d q \<cdot> |x] p \<le> d p"
hence "ad p \<le> ad (d q \<cdot> |x] p)"
by (metis a_antitone' a_subid addual.ars_r_def dpdz.domain_subid dual_order.trans)
hence "ad p \<le> ad q + |x\<rangle> ad p"
by (simp add: a_6 addual.bbox_def ds.fd_def) 
hence "ad p \<le> |x\<^sup>\<star>\<rangle> ad q"
by (metis fdia_arden h1 a_4 ads_d_def dpdz.dsg1  fdia_def meet_ord_def)
thus ?thesis
by (metis a_antitone' ads_d_def fbox_simp fdia_fbox_de_morgan_2)
qed

lemma fbox_arden_eq:  "\<nabla>x = 0 \<Longrightarrow> d q \<cdot> |x] p = d p \<Longrightarrow> |x\<^sup>\<star>] q = d p"
  by (simp add: fbox_arden antisym fbox_star_induct_eq)

lemma fbox_arden_iff: "\<nabla>x = 0 \<Longrightarrow> (d p = d q \<cdot> |x] p \<longleftrightarrow> d p = |x\<^sup>\<star>] q)"  
  by (metis fbox_arden_eq fbox_simp fbox_star_unfold_var)

lemma fbox_arden_while_iff: "\<nabla> (d t \<cdot> x) = 0 \<Longrightarrow> (d p = (d t + d q) \<cdot> |d t \<cdot> x] p \<longleftrightarrow> d p = |while t do x od] q)"
  by (metis fbox_arden_iff dka.dom_add_closed fbox_export3 while_def)  

lemma fbox_arden_whilei: "\<nabla> (d t \<cdot> x) = 0 \<Longrightarrow> (d i = (d t + d q) \<cdot> |d t \<cdot> x] i \<Longrightarrow> d i = |while t inv i do x od] q)"
  using fbox_arden_while_iff whilei_def by auto

lemma fbox_arden_whilei_iff: "\<nabla> (d t \<cdot> x) = 0 \<Longrightarrow> (d i = (d t + d q) \<cdot> |d t \<cdot> x] i \<longleftrightarrow> d i = |while t inv i do x od] q)"
  using fbox_arden_while_iff whilei_def by auto

subsection {* Nabla and Noethericity *}

lemma noether_nabla: "Noetherian x \<Longrightarrow> \<nabla> x = 0"
  by (metis nabla_closure nabla_unfold noetherian_alt)

lemma nabla_noether_iff: "Noetherian x \<longleftrightarrow> \<nabla> x = 0"
  using nabla_noether noether_nabla by blast

lemma nabla_preloeb_iff: "\<nabla> x = 0 \<longleftrightarrow> PreLoebian x"
  using Noetherian_iff_PreLoebian nabla_noether noether_nabla by blast

end

lemma rel_nabla_prop: "rel_nabla R = {} \<longleftrightarrow> (\<forall>P. P \<subseteq> relfdia R P \<longrightarrow> P = {})"
  by (metis bot.extremum_uniqueI rel_nabla_coinduct_var rel_nabla_unfold)

lemma fdia_rel_im1: "s2r ((converse R) `` P) = relfdia R (s2r P)"
  by (auto simp: Id_on_def rel_antidomain_kleene_algebra.ads_d_def rel_ad_def rel_antidomain_kleene_algebra.fdia_def Image_def converse_def)

lemma fdia_rel_im2: "s2r ((converse R) `` (r2s (rdom P))) = relfdia R P"
  by (simp add: fdia_rel_im1 rsr)

lemma wf_nabla_aux: "(P \<subseteq> (converse R) `` P \<longrightarrow> P = {}) \<longleftrightarrow> (s2r P \<subseteq> relfdia R (s2r P) \<longrightarrow> s2r P = {})"
  apply (standard, metis Domain_Id_on Domain_mono Id_on_empty fdia_rel_im1)
  using fdia_rel_im1 by fastforce

text {* A relation is noeterian if its converse is wellfounded. *}

lemma wf_nabla:  "wf (converse R) \<longleftrightarrow> rel_nabla R = {}"
  by (metis (no_types, lifting) fdia_rel_im2 rel_fdivka.nabla_unfold_eq rel_nabla_prop rel_nabla_unfold wfE_pf wfI_pf wf_nabla_aux)

end