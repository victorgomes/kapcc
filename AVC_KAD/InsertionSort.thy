theory InsertionSort
  imports  VC_KAD_Examples Lists
begin

type_synonym 'a my_store = "(nat + 'a + 'a list) store"
abbreviation "elem a \<equiv> projl (projr a)"
abbreviation "lst A \<equiv> projr (projr A)"

lemma insertion_sort:
  "PRE (\<lambda>s :: ('a :: linorder) my_store. length Ao > 0 \<and> lst (s ''A'') = Ao)
  (''i'' ::= (\<lambda>s. Inl 1));
  (WHILE (\<lambda>s. projl (s ''i'') < length (lst (s ''A'')))
   INV (\<lambda>s. sorted (take (projl (s ''i'')) (lst (s ''A''))) \<and> (lst (s ''A'') <~~> Ao))
   DO 
    (''j'' ::= (\<lambda>s. s ''i''));
    (WHILE (\<lambda>s. 0 < projl (s ''j'') \<and> 
      lst (s ''A'') ! projl (s ''j'') < lst (s ''A'') ! (projl (s ''j'') - 1))
     INV
      (\<lambda>s. sorted_but (take ((projl (s ''i'')) + 1) (lst (s ''A''))) (projl (s ''j''))
       \<and> (projl (s ''i'') < length (lst (s ''A'')))
       \<and> (projl (s ''j'') \<le>  projl (s ''i''))
       \<and> (projl (s ''j'') \<noteq> projl (s ''i'') \<longrightarrow> lst (s ''A'') ! projl (s ''j'') \<le> lst (s ''A'') ! (projl (s ''j'') + 1))
       \<and> (lst (s ''A'') <~~> Ao)
      )
     DO
      (''k'' ::= (\<lambda>s. Inr (Inl (lst (s ''A'') ! projl (s ''j'')))));
      (''A'' ::= (\<lambda>s. Inr (Inr (list_update (lst (s ''A'')) (projl (s ''j'')) 
        (lst (s ''A'') ! (projl (s ''j'') - 1))))));
      (''A'' ::= (\<lambda>s. Inr (Inr (list_update (lst (s ''A'')) (projl (s ''j'') - 1) 
        (elem (s ''k''))))));
      (''j'' ::= (\<lambda>s. Inl ((projl (s ''j'')) - 1)))
     OD);
     (''i'' ::= (\<lambda>s. Inl ((projl (s ''i'')) + 1)))
   OD)
  POST (\<lambda>s. sorted (lst (s ''A'')) \<and> (lst (s ''A'')) <~~> Ao )"
apply hoare
apply auto
  apply (metis One_nat_def not_le take_sorted_butE_n)
  apply (metis One_nat_def take_sorted_butE_0)
  apply (simp add: take_sorted_butE)
  apply (unfold sorted_equals_nth_mono sorted_but_def, auto)
  apply (smt Suc_pred diff_less_Suc le_SucE le_less_trans less_Suc_eq_le nth_list_update) 
  apply (metis (hide_lams, no_types) One_nat_def perm.trans perm_swap_list)
  apply (smt Suc_pred diff_less_Suc le_SucE le_less_trans less_Suc_eq_le nth_list_update)
  apply (smt One_nat_def le_less_trans perm.trans perm_swap_list)
done


end
