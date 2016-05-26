section {* Models of Refinement Kleene Algebra with Tests *}

theory RKAT_Models
  imports RKAT
   
begin

text {* So far only the relational model is developed. *}

definition rel_R :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where 
  "rel_R P Q = \<Union>{X. rel_kat.H P X Q}"

interpretation rel_rkat: rkat "op \<union>" "op ;" Id "{}" "op \<subseteq>" "op \<subset>" rtrancl "(\<lambda>X. Id \<inter> - X)" rel_R
  by (standard, auto simp: rel_R_def rel_kat.H_def)

end



