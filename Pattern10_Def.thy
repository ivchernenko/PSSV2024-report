theory Pattern10_Def
  imports Pattern6_Def
begin

definition P10inv where "P10inv s A1 A2 \<equiv>
 (\<forall>s1 s2.
      substate s1 s2 \<and> substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> A1 s1 s2 \<longrightarrow>
      (\<exists>s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s \<and> s2 \<noteq> s3 \<and> \<not> A2 s3)) "

lemma P10inv_rule: "
 P10inv s0 A1 A2 \<Longrightarrow> \<not> A1 s0 s \<Longrightarrow>
 P1 \<Longrightarrow> toEnvP s0 \<and> toEnvP s \<and> substate s0 s \<and> toEnvNum s0 s = 1 \<Longrightarrow>
 P10inv s A1 A2"
  apply simp
  apply(subgoal_tac "\<forall> s1. substate s1 s \<and> toEnvP s1  \<and> s1 \<noteq> s \<longrightarrow> substate s1 s0")
   apply(unfold P10inv_def)[1]
  apply(rule allI)+
  subgoal for s1 s2
    apply(cases "s2=s")
     apply (metis One_nat_def toEnvNum_eq_imp_eq2)
    apply(erule allE[of _ s1])
    apply(rotate_tac -1)
    apply(erule allE[of _ s2])
    using substate_trans by blast
  by (metis (full_types) one_is_add substate_linear substate_toEnvNum_id toEnvNum3)

lemma P10_einv2req: "
P10inv s0 A1 A2 \<Longrightarrow>
 toEnvP s0 \<and> toEnvP s \<and>  substate s0 s \<and> toEnvNum s0 s = 1 \<Longrightarrow>
 substate s1 s2 \<and>    substate s2 s \<and>     toEnvP s1 \<and>     toEnvP s2 \<and>     toEnvNum s1 s2 = 1 \<and>     s2 \<noteq> s \<and> A1 s1 s2 \<and> A3 s \<and>
   (\<forall>s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s \<and> s2 \<noteq> s4 \<and> s4 \<noteq> s \<longrightarrow> A2 s4) \<longrightarrow>
 A4 s
"
  apply(unfold P10inv_def)
  apply simp
  apply(erule allE[of _ s1])
  apply(erule allE[of _ s2])
  apply(rule impI)
  apply(erule impE)
  using substate_linear substate_refl toEnvNum3 toEnvNum_eq_imp_eq2
   apply (metis (no_types, lifting) add_is_1)
  by (metis n_not_Suc_n substate_antisym substate_trans toEnvNum_id)

definition P10' where "P10' s A11 A12 A2 A3 A4 \<equiv> P6_4 s A11 A12 (\<lambda> s3. \<not>A2 s3) (\<lambda> s4. A2 s4 \<and> A4 s4 \<or> A3 s4)"

definition P10'inv where "P10'inv s w b1 b2 b3 b4 A11 A12 A2 A3 A4 \<equiv>
 P6_4inv s w b1 b2 A11 A12 (\<lambda> s3. \<not>A2 s3) (\<lambda> s4. (A2 s4 \<and> A4 s4 \<or> A3 s4) \<and> (b3 \<longrightarrow> A2 s4 \<and> A4 s4) \<and> (b4 \<longrightarrow> A3 s4))"

lemma P10'_rule_gen: "
P10'inv s0 w b1 b2 b3 b4 A11 A12 A2 A3 A4 \<Longrightarrow> consecutive s0 s \<Longrightarrow>
(((b1 \<or> (A2 s \<and> A4' s \<or> A3' s) \<and> (b3' \<longrightarrow> A2 s \<and> A4' s) \<and> (b4' \<longrightarrow> A3' s) \<or> w' \<and> \<not> A2 s ) \<and> (
(((\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A4 s1 \<longrightarrow> A4' s1) \<or> b4 \<and> (\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A3 s1 \<longrightarrow> A3' s1))
 \<and> ((\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A3 s1 \<longrightarrow> A3' s1) \<or> b3 \<and> (\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A4 s1 \<longrightarrow> A4' s1))
\<and> (b3' \<longrightarrow> b3 \<and>  (\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A4 s1 \<longrightarrow> A4' s1)) \<and>
(b4' \<longrightarrow> b4 \<and>  (\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A3 s1 \<longrightarrow> A3' s1)))
 \<and>
( \<not> w \<or> (A2 s \<and> A4' s \<or> A3' s) \<and> (b3' \<longrightarrow> A2 s \<and> A4' s) \<and> (b4' \<longrightarrow> A3' s) \<or> w' \<and> \<not> A2 s))) \<and>
 (b1' \<longrightarrow> b2 \<or> \<not>A12 s)) \<and>
 (b2' \<longrightarrow>\<not> A11 s)  \<Longrightarrow>
P10'inv s w' b1' b2' b3' b4' A11 A12 A2 A3' A4' "
  apply(unfold P10'inv_def)
  apply(erule P6_4_rule_gen)
   apply simp
  apply(erule conjE)
  subgoal premises prems1
    apply(rule conjI)
     apply(insert prems1(1,2))[1]
     apply(erule conjE)
    subgoal premises prems2
      apply(rule conjI)
       apply(insert prems2(1,2))[1]
       apply(erule conjE)
      subgoal premises prems3
        apply(rule conjI)
         apply(insert prems3(1,2))[1]
         apply simp
        apply(insert prems3(1,3))
        apply(rule conjI)
         apply simp
        apply(erule conjE)
        subgoal premises prems4
          apply(rule conjI)
           apply(insert prems4(1,2))[1]
           apply(rule all_disj_inv_rule)
           apply auto[1]
          apply(insert prems4(1,3))
          apply auto[1]
          done
        done
      apply(insert prems2(1,3))
      apply auto
      done
    apply(insert prems1(1,3))
    apply auto
    done
  done

definition P10'inv1 where "P10'inv1 s w b1 b2 A11 A12 A2 A3 A4 \<equiv>
 P6_4inv s w b1 b2 A11 A12 (\<lambda> s3. \<not>A2 s3) (\<lambda> s4. (A2 s4 \<and> A4 s4 \<or> A3 s4))"

lemma P10'1_rule_gen: "
P10'inv1 s0 w b1 b2  A11 A12 A2 A3 A4 \<Longrightarrow> consecutive s0 s \<Longrightarrow>
(((b1 \<or> (A2 s \<and> A4' s \<or> A3' s)  \<or> w' \<and> \<not> A2 s ) \<and> (
((\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A4 s1 \<longrightarrow> A4' s1)
 \<and> (\<forall> s1. toEnvP s1 \<and> substate s1 s0 \<and> A3 s1 \<longrightarrow> A3' s1)) \<and>
( \<not> w \<or> (A2 s \<and> A4' s \<or> A3' s)  \<or> w' \<and> \<not> A2 s))) \<and>
 (b1' \<longrightarrow> b2 \<or> \<not>A12 s)) \<and>
 (b2' \<longrightarrow>\<not> A11 s)  \<Longrightarrow>
P10'inv1 s w' b1' b2' A11 A12 A2 A3' A4' "
  apply(unfold P10'inv1_def)
  apply(erule P6_4_rule_gen)
   apply auto
  done

lemma P10'1_einv2req_gen: "P10'inv1  s w b1 b2 A11 A12 A2 A3 A4 \<Longrightarrow>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A4 s1 \<longrightarrow> A4' s1) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and> A3 s1 \<longrightarrow> A3' s1) \<Longrightarrow>
 P10' s A11 A12 A2 A3' A4'"
  apply(unfold P10'inv1_def P10'_def)
  apply(erule P6_4_einv2req_gen)
  apply auto
  done

lemma P10'1_rule: "
P10'inv1 s0 w b1 b2  A11 A12 A2 A3 A4 \<Longrightarrow> consecutive s0 s \<Longrightarrow>
(((b1 \<or> (A2 s \<and> A4 s \<or> A3 s)  \<or> w' \<and> \<not> A2 s ) \<and> (
( \<not> w \<or> (A2 s \<and> A4 s \<or> A3 s)  \<or> w' \<and> \<not> A2 s))) \<and>
 (b1' \<longrightarrow> b2 \<or> \<not>A12 s)) \<and>
 (b2' \<longrightarrow>\<not> A11 s)  \<Longrightarrow>
P10'inv1 s w' b1' b2' A11 A12 A2 A3 A4 "
  using P10'1_rule_gen apply auto
  done

lemma P10'1_einv2req: "P10'inv1  s w b1 b2 A11 A12 A2 A3 A4 \<Longrightarrow>
 P10' s A11 A12 A2 A3 A4"
  using P10'1_einv2req_gen apply auto
  done 
          

end



 