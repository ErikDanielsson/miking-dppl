include "graph-experiment-2.mc"
include "stdlib::hashmap.mc"

lang HRMResample = PValInterface
  -- type HRMState x = ([SomePAssumeRef], x)
  type NodeID = Int
  type BranchState a =
    { assumes : [PAssumeRef Repertoire]
    , x : a
    }

  type TopState a b =
    { nodeAssumes : HashMap NodeID (PAssumeRef Repertoire)
    , leftChildren : HashMap NodeID (SubmodelRef BranchState)
    , rightChildren : HashMap NodeID (SubmodelRef BranchState)
    , parent : HashMap NodeID (SubmodelRef BranchState)
    , globalParamA : a
    , globalParamB : b
    }

  sem simpleStore : all a. HRMState () -> PAssumeRef a -> SimpleState ()
  sem simpleStore rs = | r -> (snoc rs.0 (SomePAssumeRef r), rs.1)

  sem topStore : all a. NodeID -> NodeID -> HRMState () -> PAssumeRef a -> HRMState ()
  sem topStore label = | pLabel rs r ->
    let 
  (snoc rs.0 (SomePAssumeRef r), rs.1)

  sem simpleExport : all x2. HRMState () -> PExportRef x2 -> SimpleState (PExportRef x2)
  sem simpleExport rs = | r -> (rs.0, r)

  sem simpleResample : all x. Float -> PValInstance Partial (HRMState x) -> PValInstance Partial (SimpleState x)
  sem simpleResample globalProb = | instance ->
    let st = getSt instance in
    let doResample = lam instance. lam someAssume.
      match someAssume with SomePAssumeRef x in
      resampleAssume (lam d. lam. d) x instance in
    if bernoulliSample globalProb then
      foldl doResample instance st.0
    else
      doResample instance (_chooseUniform st.0)

  sem simpleRead : all x. all complete. PValInstance complete (HRMState (PExportRef x)) -> x
  sem simpleRead = | instance ->
    readPreviousExport (getSt instance).1 instance
end