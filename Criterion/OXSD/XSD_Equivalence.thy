theory XSD_Equivalence
imports OXSD_Criterion "../Incomplete_Criteria"
begin

context Sloped_Graph
begin


(*A proof that SD implies  OXSD*)


(**SD implies XSD**)
theorem SDdescending_implies_OXSDdescending:
  "SDdescending \<Longrightarrow> OXSDdescending"
  unfolding SDdescending_def OXSDdescending_def
proof clarify
  fix Node1 edge1
  assume SD: "\<forall>Node1 edge1. scsg Node1 edge1 \<longrightarrow> (\<exists>lab. wfLabF Node1 lab \<and> decreasingPCC edge1 lab)"
  assume scsg: "scsg Node1 edge1"
  
  (* 1. Sanitize the edge relation to guarantee strict node inclusion *)
  define edge1' where "edge1' \<equiv> \<lambda>x y. edge1 x y \<and> x \<in> Node1 \<and> y \<in> Node1"
  
  have scsg': "scsg Node1 edge1'"
    using scsg Graph_scg_restrict unfolding scsg_def edge1'_def Graph.subgr_def
    by auto
    
  (* 2. Apply SDdescending to the sanitized subgraph *)
  from SD scsg' obtain lab where wf: "wfLabF Node1 lab" and pcc: "decreasingPCC edge1' lab"
    by blast
    
  (* 3. Construct XSD witnesses (Singletons) *)
  define lab' where "lab' \<equiv> \<lambda>nd. {lab nd}"
  define f where "f \<equiv> \<lambda>(nd::'node) nd' (P::'pos). lab nd'"
  
  show "\<exists>lab' f. wfLabFS Node1 lab' \<and> decreasingPCSC Node1 edge1 lab' f"
  proof (intro exI conjI)
    show "wfLabFS Node1 lab'"
      using wf unfolding wfLabF_def wfLabFS_def lab'_def by blast
      
    show "decreasingPCSC Node1 edge1 lab' f"
      unfolding decreasingPCSC_def
    proof (intro conjI allI impI)
      (* A: RRSetChoice *)
      show "RRSetChoice Node1 edge1 lab' f"
        using pcc unfolding decreasingPCC_def RRSetChoice_def lab'_def f_def edge1'_def by auto
        
      (* B: The Slice Condition *)
      fix NNode eedge
      assume "Graph.subgr NNode eedge (extgrS Node1 lab') (extgrR edge1 f) \<and>
              Graph.scg NNode eedge \<and>
              (\<forall>nd nd'. {nd, nd'} \<subseteq> Node1 \<and> edge1 nd nd' \<longrightarrow> 
                     (\<exists>P P'. {(nd, P), (nd', P')} \<subseteq> NNode \<and> eedge (nd, P) (nd', P')))"

      hence subgr: "Graph.subgr NNode eedge (extgrS Node1 lab') (extgrR edge1 f)"
        and cover: "\<forall>nd nd'. {nd, nd'} \<subseteq> Node1 \<and> edge1 nd nd' \<longrightarrow> 
                     (\<exists>P P'. {(nd, P), (nd', P')} \<subseteq> NNode \<and> eedge (nd, P) (nd', P'))"
        by auto
                     
      (* Obtain the decreasing edge, which is GUARANTEED to be in Node1 thanks to edge1' *)
      from pcc obtain nd_d nd_d' where decr: "edge1' nd_d nd_d'" "RR (nd_d, lab nd_d) (nd_d', lab nd_d') Decr"
        unfolding decreasingPCC_def by blast
        
      have nodes_in: "{nd_d, nd_d'} \<subseteq> Node1" and orig_edge: "edge1 nd_d nd_d'"
        using decr(1) unfolding edge1'_def by auto
        
      (* Force the slice to cover this specific decreasing edge *)
      obtain P P' where in_slice: "{(nd_d, P), (nd_d', P')} \<subseteq> NNode" "eedge (nd_d, P) (nd_d', P')"
        using cover nodes_in orig_edge by blast
        
      (* Extract the exact positions from the singleton sets *)
      have "P = lab nd_d" and "P' = lab nd_d'"
        using subgr in_slice(1) unfolding Graph.subgr_def extgrS_def lab'_def by auto
        
      (* Output the final existential witnesses *)
      show "\<exists>nd_P nd_P'. {nd_P, nd_P'} \<subseteq> NNode \<and> eedge nd_P nd_P' \<and> RR nd_P nd_P' Decr"
        apply (intro exI conjI)
        using in_slice decr(2) \<open>P = lab nd_d\<close> \<open>P' = lab nd_d'\<close> by auto
    qed
  qed
qed



(**EQUIVALENCE PROOFS**)
(**This entails proving that the underlying "sliced" definition is equivalent to the same subgraph requirements for OXSD **)
lemma is_slice_eq_subgr:
  assumes scsg: "scsg Node1 edge1" 
  and wf: "wfLabFS Node1 lab" 
  and rr: "RRSetChoice Node1 edge1 lab f"
  shows "is_slice Node1 edge1 lab f NNode eedge \<longleftrightarrow>
         (Graph.subgr NNode eedge (extgrS Node1 lab) (extgrR edge1 f) \<and>
          (\<forall>nd P nd' P'. eedge (nd, P) (nd', P') \<longrightarrow> {(nd, P), (nd', P')} \<subseteq> NNode) \<and>
          (\<forall>nd nd'. {nd,nd'} \<subseteq> Node1 \<and> edge1 nd nd' \<longrightarrow>
             (\<exists>P P'. {(nd, P), (nd', P')} \<subseteq> NNode \<and> eedge (nd, P) (nd', P'))))"
  (is "?LHS \<longleftrightarrow> ?RHS")
proof 
  assume L: "?LHS"
  show "?RHS"
  proof -
    have nnode_bound: "NNode \<subseteq> {(nd, P). nd \<in> Node1 \<and> P \<in> lab nd}"
      using L unfolding is_slice_def by simp
    have bounds: "\<forall>nd P nd' P'. eedge (nd, P) (nd', P') \<longrightarrow> {(nd, P), (nd', P')} \<subseteq> NNode"
      using L unfolding is_slice_def by blast

    have proj: "\<forall>nd P nd' P'. eedge (nd, P) (nd', P') \<longrightarrow> edge1 nd nd' \<and> f nd nd' P = P'"
      using L unfolding is_slice_def by blast
    have cover: "\<forall>nd nd'. {nd,nd'} \<subseteq> Node1 \<and> edge1 nd nd' \<longrightarrow> (\<exists>P P'. {(nd, P), (nd', P')} \<subseteq> NNode \<and> eedge (nd, P) (nd', P'))"
      using L unfolding is_slice_def by blast
      
    have subgr: "Graph.subgr NNode eedge (extgrS Node1 lab) (extgrR edge1 f)"
      using proj L nnode_bound 
      unfolding is_slice_def Graph.subgr_def extgrS_def extgrR_def  by blast+
      
    thus ?RHS using cover bounds by blast
  qed
next
  assume R: "?RHS"
  show "?LHS"
  proof -
    have subgr: "Graph.subgr NNode eedge (extgrS Node1 lab) (extgrR edge1 f)" 
      using R by blast
    have bounds: "\<forall>nd P nd' P'. eedge (nd, P) (nd', P') \<longrightarrow> {(nd, P), (nd', P')} \<subseteq> NNode"
      using R by simp

    have cover: "(\<forall>nd nd'. {nd,nd'} \<subseteq> Node1 \<and> edge1 nd nd' \<longrightarrow> (\<exists>P P'. {(nd, P), (nd', P')} \<subseteq> NNode \<and> eedge (nd, P) (nd', P')))"
      using R by blast
    
    have nnode_bound: "NNode \<subseteq> {(nd, P). nd \<in> Node1 \<and> P \<in> lab nd}"
      using subgr unfolding Graph.subgr_def extgrS_def by auto

    have subgr_ExtG: "Graph.subgr NNode eedge ExtG_Nodes ExtG_Edges"
      unfolding Graph.subgr_def ExtG_Nodes_def ExtG_Edges_def
      apply (simp add: split_beta, intro conjI) (* Flattens the lambda pair cases instantly *)
      subgoal using nnode_bound wf assms(1)  unfolding wfLabFS_def scsg_def Graph.subgr_def by auto
      subgoal 
      proof(intro allI impI) 
        fix nd P nd' P'
        assume eedge: "eedge (nd, P) (nd', P')"
        
        (* A: Extract the nodes from the ExtgrS subgr constraint *)
        have nodes_in: "nd \<in> Node1" "nd' \<in> Node1" "P \<in> lab nd"
          using eedge bounds nnode_bound by fastforce+

        (* B: Extract the function mapping from ExtgrR *)
        have ext_R: "extgrR edge1 f (nd, P) (nd', P')"
          using subgr eedge unfolding Graph.subgr_def by blast
        hence edge1_f: "edge1 nd nd'" "f nd nd' P = P'"
          unfolding extgrR_def by (auto simp: split_beta)
        
        (* C: Prove the two ExtG requirements *)
        have e1: "edge nd nd'"
          using scsg edge1_f(1) unfolding scsg_def Graph.subgr_def by blast
        have e2: "RR (nd, P) (nd', P') Main \<or> RR (nd, P) (nd', P') Decr"
          using rr edge1_f nodes_in unfolding RRSetChoice_def by blast
          
        show "edge nd nd' \<and> (RR (nd, P) (nd', P') Main \<or> RR (nd, P) (nd', P') Decr)"
          using e1 e2 by blast
      qed .

    have proj: "\<forall>nd P nd' P'. eedge (nd, P) (nd', P') \<longrightarrow> {(nd, P), (nd', P')} \<subseteq> NNode \<and> edge1 nd nd' \<and> f nd nd' P = P'"
       using subgr bounds unfolding Graph.subgr_def extgrR_def by (auto simp: split_beta)

    show ?LHS
      unfolding is_slice_def
      using nnode_bound subgr_ExtG proj cover by blast
  qed
qed

(*Key lemma*)
lemma descending_PCSC_equiv:
  assumes "scsg Node1 edge1" "wfLabFS Node1 lab"
  shows "descending_PCSC_sliced Node1 edge1 lab f \<longleftrightarrow> decreasingPCSC Node1 edge1 lab f"
  (is "?LHS \<longleftrightarrow> ?RHS")
proof (cases "RRSetChoice Node1 edge1 lab f")
  case False
  thus ?thesis unfolding descending_PCSC_sliced_def decreasingPCSC_def by simp
next
  case True
  show ?thesis
  proof
    assume L: "?LHS"
    show "?RHS"
      unfolding decreasingPCSC_def
    proof safe
      show "RRSetChoice Node1 edge1 lab f" using True by simp
      
      fix NNode eedge
      assume subgr: "Graph.subgr NNode eedge (extgrS Node1 lab) (extgrR edge1 f)"
      assume scg: "Graph.scg NNode eedge"
      assume cover: "\<forall>nd nd'. {nd, nd'} \<subseteq> Node1 \<and> edge1 nd nd' \<longrightarrow> (\<exists>P P'. {(nd, P), (nd', P')} \<subseteq> NNode \<and> eedge (nd, P) (nd', P'))"
      
      (* Restrict eedge so it perfectly fits is_slice bounds *)
      define eedge' where "eedge' \<equiv> \<lambda>x y. eedge x y \<and> x \<in> NNode \<and> y \<in> NNode"
      
      have "is_slice Node1 edge1 lab f NNode eedge'"
        unfolding is_slice_eq_subgr[OF assms True]
      proof (intro conjI)
        show "Graph.subgr NNode eedge' (extgrS Node1 lab) (extgrR edge1 f)"
          using subgr unfolding Graph.subgr_def eedge'_def by auto
        show "\<forall>nd P nd' P'. eedge' (nd, P) (nd', P') \<longrightarrow> {(nd, P), (nd', P')} \<subseteq> NNode"
          unfolding eedge'_def by auto
        show "\<forall>nd nd'. {nd, nd'} \<subseteq> Node1 \<and> edge1 nd nd' \<longrightarrow> (\<exists>P P'. {(nd, P), (nd', P')} \<subseteq> NNode \<and> eedge' (nd, P) (nd', P'))"
          using cover unfolding eedge'_def by fast
      qed
      
      moreover have "Graph.scg NNode eedge'"
        using scg Graph_scg_restrict unfolding eedge'_def by auto
        
      ultimately have "decreasing_slice NNode eedge'"
        using L unfolding descending_PCSC_sliced_def by blast
        
      thus "\<exists>nd_P nd_P'. {nd_P, nd_P'} \<subseteq> NNode \<and> eedge nd_P nd_P' \<and> RR nd_P nd_P' Decr"
        unfolding decreasing_slice_def eedge'_def by blast
    qed
  next
    assume R: "?RHS"
    show "?LHS"
      unfolding descending_PCSC_sliced_def
    proof safe
      show "RRSetChoice Node1 edge1 lab f" using True by simp
      
      fix NNode eedge
      assume is_slice: "is_slice Node1 edge1 lab f NNode eedge"
      assume scg: "Graph.scg NNode eedge"
      
      have "Graph.subgr NNode eedge (extgrS Node1 lab) (extgrR edge1 f)"
       and "\<forall>nd nd'. {nd, nd'} \<subseteq> Node1 \<and> edge1 nd nd' \<longrightarrow> (\<exists>P P'. {(nd, P), (nd', P')} \<subseteq> NNode \<and> eedge (nd, P) (nd', P'))"
        using is_slice unfolding is_slice_eq_subgr[OF assms True] by blast+
        
      thus "decreasing_slice NNode eedge"
        using R scg unfolding decreasingPCSC_def decreasing_slice_def by auto
    qed
  qed
qed

(*Equivalence between the new criterion and it's legacy definition*)

theorem "XSDdescending \<longleftrightarrow> OXSDdescending"
  unfolding XSDdescending_def OXSDdescending_def
  using descending_PCSC_equiv by blast

end
end
