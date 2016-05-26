section {* Verification Component Based on Refinement KAT *}

theory VC_RKAT
  imports "../RKAT_Models"

begin

text {* The store model is taken from VCKAT *}

subsection {* Derivation of Three Assignment Laws. *}

lemma R_assign: "(\<forall>s. P s \<longrightarrow> Q (s (v := e s))) \<Longrightarrow> (v ::= e) \<subseteq> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
proof - 
  assume "(\<forall>s. P s \<longrightarrow> Q (s (v := e s)))"
  hence "rel_kat.H \<lceil>P\<rceil> (v ::= e) \<lceil>Q\<rceil>"
    by (rule H_assign_var)
  thus ?thesis
    by (rule rel_rkat.R2)
qed

lemma R_assignr: "(\<forall>s. Q' s \<longrightarrow> Q (s (v := e s))) \<Longrightarrow> (rel_R \<lceil>P\<rceil> \<lceil>Q'\<rceil>) ; (v ::= e) \<subseteq> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"  
  by (metis H_assign_var rel_kat.H_seq rel_rkat.R1 rel_rkat.R2)   

lemma R_assignl: "(\<forall>s. P s \<longrightarrow> P' (s (v := e s))) \<Longrightarrow> (v ::= e) ; (rel_R \<lceil>P'\<rceil> \<lceil>Q\<rceil>) \<subseteq> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  by (metis H_assign_var rel_kat.H_seq rel_rkat.R1 rel_rkat.R2)

subsection {* Simplifications *}

lemma R_cons: "(\<forall>s. P s \<longrightarrow> P' s) \<Longrightarrow> (\<forall>s. Q' s \<longrightarrow> Q s) \<Longrightarrow> rel_R \<lceil>P'\<rceil> \<lceil>Q'\<rceil> \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  by (simp add: rel_rkat.R1 rel_rkat.R2 sH_cons_1 sH_cons_2)

end


