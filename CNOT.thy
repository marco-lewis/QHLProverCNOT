section\<open>CNOT in QHLProver\<close>

theory CNOT
  imports QHLProver.Gates 
  QHLProver.Partial_State
  QHLProver.Quantum_Hoare
  QHLProver.Quantum_Program
  QHLProver.Grover
  QHLProver.Complex_Matrix
begin

subsection\<open>Environment Settings\<close>

locale cnot_state = state_sig +
  fixes n :: nat  (* number of qubits *)
  assumes n: "n = (2::nat)"
  assumes dims_def: "dims = [2,2]"
begin

definition N where
  "N = (2::nat) ^ n"

lemma N_4:
  "N == 4" using N_def n by auto

lemma d_4:
  "d == 4"
  using d_def dims_def by auto

lemma N_d:
  "N == d"
  using d_4 N_4 by auto


subsection\<open>State Vectors and Properties\<close>

abbreviation proj :: "complex vec \<Rightarrow> complex mat" where
  "proj v \<equiv> outer_prod v v"

definition ket_10 :: "complex vec" where
  "ket_10 = Matrix.vec N (\<lambda>i . if i = 2 then 1 else 0)"

lemma ket_10_dim [simp]:
  "ket_10 \<in> carrier_vec N"
  "dim_vec ket_10 = N"
  by (simp add: ket_10_def)+

lemma ket_10_eval:
  "i < N \<Longrightarrow> ket_10 $ i = (if i = 2 then 1 else 0)"
  by (simp add: ket_10_def)

definition ket_11 :: "complex vec" where
  "ket_11 = Matrix.vec N (\<lambda>i. if i = 3 then 1 else 0)"

lemma ket_11_dim [simp]:
  "ket_11 \<in> carrier_vec N"
  "dim_vec ket_11 = N"
  by (simp add: ket_11_def)+

lemma ket_11_eval:
  "i < N \<Longrightarrow> ket_11 $ i = (if i = 3 then 1 else 0)"
  by (simp add: ket_11_def)

subsection\<open>Precondition and Postcondition\<close>
definition proj_10 where
  "proj_10 = proj ket_10"

lemma norm_pre:
  "inner_prod ket_10 ket_10 = 1"
  unfolding ket_10_def
  apply (simp add: scalar_prod_def)
  using sum_only_one_neq_0[of "{0..<N}" 2 "\<lambda>i. (if i = 2 then 1 else 0) * cnj (if i = 2 then 1 else 0)"] N_def
  n by auto

lemma qp_pre:
  "is_quantum_predicate proj_10"
  unfolding is_quantum_predicate_def
proof (intro conjI)
  show "proj_10 \<in> carrier_mat d d" using proj_10_def ket_10_def N_d by auto
  show "positive proj_10"
    using positive_same_outer_prod
    unfolding proj_10_def ket_10_def 
    by auto
  show "proj_10 \<le>\<^sub>L 1\<^sub>m d"
    unfolding proj_10_def
    using norm_pre N_d outer_prod_le_one ket_10_def
    by auto
qed

definition proj_11 where
  "proj_11 = proj ket_11"

lemma norm_post:
  "inner_prod ket_11 ket_11 = 1"  
  unfolding ket_11_def
  apply (simp add: scalar_prod_def)
  using sum_only_one_neq_0[of "{0..<N}" 3 "\<lambda>i. (if i = 3 then 1 else 0) * cnj (if i = 3 then 1 else 0)"] N_def
  n by auto

lemma qp_post:
  "is_quantum_predicate proj_11"
  unfolding is_quantum_predicate_def
proof (intro conjI)
  show "proj_11 \<in> carrier_mat d d" using proj_11_def ket_11_def N_d by auto
  show "positive proj_11"
    using positive_same_outer_prod
    unfolding proj_11_def ket_11_def 
    by auto
  show "proj_11 \<le>\<^sub>L 1\<^sub>m d"
    unfolding proj_11_def
    using norm_post N_d outer_prod_le_one ket_11_def
    by auto
qed

subsection\<open>CNOT Gate and Properties\<close>
definition cnot :: "complex mat" where
  "cnot = mat N N (\<lambda>(i,j). 
    if i=j then 
      (if (i=0 \<or> i=1) then 1 else 0)
      else (if (i=2 \<and> j=3) \<or> (i=3 \<and> j=2)
        then 1 else 0))"

lemma cnot_dim:
   "cnot \<in> carrier_mat N N"
  unfolding cnot_def by auto

lemma hermitian_cnot:
  "hermitian cnot"
  by (auto simp add: hermitian_def cnot_def adjoint_eval)

lemma cnot_cnot_eq_id:
  shows "cnot *  cnot = 1\<^sub>m N"
  apply(rule eq_matI,simp)
  apply(auto simp add: carrier_matD[OF cnot_dim] scalar_prod_def)
  unfolding cnot_def
  apply(simp_all)
  apply(case_tac "j = 3")
  subgoal for j
    unfolding N_4
    by (simp add: sum_only_one_neq_0[of _ "2"])
  apply (case_tac "j = 2")
  subgoal for j
    unfolding N_4
    by (simp add: sum_only_one_neq_0[of _ "3"])
  apply (case_tac "j = 1")
  subgoal for j
    unfolding N_4
    by (simp add: sum_only_one_neq_0[of _ "1"])
  subgoal for j
    unfolding N_4
    by (simp add: sum_only_one_neq_0[of _ "0"])
  done

lemma unitary_cnot:
  "unitary cnot"
proof -
  have "cnot \<in> carrier_mat N N" 
    using cnot_dim by auto
  moreover have "cnot * adjoint cnot = cnot * cnot"
    using hermitian_cnot unfolding hermitian_def by auto
  moreover have "cnot * cnot = 1\<^sub>m N" 
    using cnot_cnot_eq_id by auto
  ultimately show ?thesis 
    unfolding unitary_def inverts_mat_def by auto
qed

definition cnot_circ :: "com" where
  "cnot_circ = Utrans cnot"

lemma well_com_cnot:
  "well_com cnot_circ"
  unfolding cnot_circ_def 
  using unitary_cnot cnot_dim N_4 d_4 
  by auto


subsection\<open>Deduction\<close>
subsubsection\<open>Sanity Check with Identity\<close>
definition id :: "complex mat" where
  "id = mat N N (\<lambda>(i,j). if i=j then 1 else 0)"

lemma id_times_11:
  "id *\<^sub>v ket_11 = ket_11"
  by (auto simp add: id_def ket_11_def
    scalar_prod_def sum_only_one_neq_0)

thm scalar_prod_def
thm sum_only_one_neq_0[of _ "1" "\<lambda>i. i+ 5"]

subsubsection\<open>CNOT Correctness Deductions\<close>
lemma cnot_times_11:
  "cnot *\<^sub>v ket_11 = ket_10"
  apply (rule eq_vecI, simp)
  apply(auto simp add: carrier_matD[OF cnot_dim] scalar_prod_def)
  unfolding cnot_def ket_11_def ket_10_def N_4 scalar_prod_def
    by (simp add: sum_only_one_neq_0[of _ "3"])

(*
Alternate attempt
lemma sub:
  "k \<noteq> 2 \<Longrightarrow> (cnot *\<^sub>v ket_11) $ k = 0"
  using cnot_def ket_11_def scalar_prod_def by auto

lemma sub2:
  "k = 2 \<Longrightarrow> (cnot *\<^sub>v ket_11) $ k = 1"
  by (auto simp add: cnot_def ket_11_def 
  scalar_prod_def)

proof -
  have "dim_vec (cnot *\<^sub>v ket_11) = dim_vec ket_10" 
    using cnot_def by auto
  moreover have "\<And>i. i < dim_vec ket_10 \<Longrightarrow>
         (cnot *\<^sub>v ket_11) $ i = ket_10 $ i"
    using ket_10_def sub sub2 by auto
  ultimately show ?thesis by auto
qed
*)

lemma cnot_times_post_is_pre:
  "adjoint cnot * proj_11 * cnot = proj_10"
proof -
  let ?m = "cnot"
  have eq: "adjoint ?m = ?m" 
    using hermitian_def hermitian_cnot by auto
  {
    let ?p = "proj_11"
    have "?m * ?p * ?m = outer_prod ket_10 ket_10"
      unfolding proj_11_def
      using ket_11_def cnot_dim cnot_times_11 eq
      apply (subst outer_prod_left_right_mat[of _ N _ N  _ N _ N])
      by auto
  }
  note p = this
  have "adjoint cnot * proj_11 * cnot = ?m * proj_11 *?m"
    using eq by auto
  also have "... = proj_10"
    unfolding proj_10_def
    using p
    by auto
  finally show ?thesis by auto
qed

lemma adjoint_deduction:
  "\<turnstile>\<^sub>p         
   {adjoint cnot * proj_11 * cnot}
    cnot_circ
   {proj_11}"
  unfolding cnot_circ_def using
  hoare_partial.intros(2) 
  unitary_cnot qp_post
  by auto

lemma prog_partial_deduct:
  "\<turnstile>\<^sub>p         
   {proj_10}
    cnot_circ
   {proj_11}"
  using cnot_times_post_is_pre adjoint_deduction by auto

theorem prog_partial_correct:
  "\<Turnstile>\<^sub>p
   {proj_10}
    cnot_circ
   {proj_11}"
  using 
  prog_partial_deduct 
  well_com_cnot qp_pre qp_post 
  hoare_partial_sound by auto

end

end
