include "graph-experiment-2.mc"

lang SimpleResample = PValInterface
  type SimpleState x = ([SomePAssumeRef], x)

  sem simpleStore : all a. SimpleState () -> PAssumeRef a -> SimpleState ()
  sem simpleStore rs = | r -> (snoc rs.0 (SomePAssumeRef r), rs.1)

  sem simpleExport : all x2. SimpleState () -> PExportRef x2 -> SimpleState (PExportRef x2)
  sem simpleExport rs = | r -> (rs.0, r)

  sem simpleResample : all x. Float -> PValInstance Partial (SimpleState x) -> PValInstance Partial (SimpleState x)
  sem simpleResample globalProb = | instance ->
    let st = getSt instance in
    let doResample = lam instance. lam someAssume.
      match someAssume with SomePAssumeRef x in
      resampleAssume (lam d. lam. d) x instance in
    if bernoulliSample globalProb then
      foldl doResample instance st.0
    else
      doResample instance (_chooseUniform st.0)

  sem simpleRead : all x. all complete. PValInstance complete (SimpleState (PExportRef x)) -> x
  sem simpleRead = | instance ->
    readPreviousExport (getSt instance).1 instance
end

type BranchState =
  { assumes : [PAssumeRef Repertoire]
  }

type TopState a b =
  { assumes : Map ID
    { inNode : PAssumeRef Repertoire
    , above : Option (SubmodelRef BranchState)
    , belowLeft : Option (SubmodelRef BranchState)
    , belowRight : Option (SubmodelRef BranchState)
    }
  , globalParamA : a
  , globalParamB : b
  }
type TopState a b =
  { nodeAssumes : Map ID (PAssumeRef Repertoire)
  , leftChildren : Map ID (SubmodelRef BranchState)
  , rightChildren : Map ID (SubmodelRef BranchState)
  , parent : Map ID (SubmodelRef BranchState)
  , globalParamA : a
  , globalParamB : b
  }
instantiate : (PValState (TopState () ()) -> PValState TopState)
p_bind st (lam branchState. /- insert branchState in TopState relative to parent *and* child -/) {assumes = []} #frozen"f"