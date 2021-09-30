#!/bin/bash

scc src/IdealWorld.v src/RealWorld.v src/Keys.v src/Messages.v src/MessageEq.v src/Simulation.v src/StepRelations.v \
    src/ModelCheck/ModelCheck.v src/ModelCheck/InvariantSearch.v \
    src/ModelCheck/SteppingTactics.v src/ModelCheck/ProtocolFunctions.v
