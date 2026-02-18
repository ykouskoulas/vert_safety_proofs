# Guaranteed-safe vertical collision avoidance maneuvers for non-deterministic aircraft dynamics

## What is this?

This repository contains a peer-reviewed publication that develops an
approach to analyze the safety of maneuvers used for aircraft
collision avoidance maneuvers. The paper develops detailed mathematics
for the analysis of vertical maneuvers, describes how they can be
composed with different types of horizontal maneuvers, and includes
machine checked proofs that guarantee the safety and correctness of
this approach. This work was developed as part of the independent
evaluation of the FAA's next-generation air-traffic collision
avoidance system, ACAS X.

## Documentation

The paper is titled

*"Formally Verified Safe Vertical Maneuvers for Non-deterministic,
Accelerating Aircraft Dynamics"*

and was presented at the 8th international conference for Interactive
Theorem Proving in 2017.

Abstract:

We present the formally veriﬁed predicate and strategy used
to independently evaluate the safety of the ﬁnal version (Run 15) of the
FAAs next-generation air-traﬃc collision avoidance system, ACAS X.
This approach is a general one that can analyze simultaneous vertical
and horizontal maneuvers issued by aircraft collision avoidance systems.
The predicate is specialized to analyze sequences of vertical maneuvers,
and in the horizontal dimension is modular, allowing it to be safely
composed with separately analyzed horizontal dynamics. Unlike previ-
ous eﬀorts, this approach enables analysis of aircraft that are turning,
and accelerating non-deterministically. It can also analyze the safety of
coordinated advisories, and encounters with more than two aircraft. We
provide results on the safety evaluation of ACAS X coordinated collision
avoidance on a subset of the system state space. This approach can also
be used to establish the safety of vertical collision avoidance maneuvers
for other systems with complex dynamics.

## To build and check the proofs

```
olympia:vert_safety_proofs yak$ coqtop --version
The Coq Proof Assistant, version 8.5pl2 (October 2016)
compiled on Oct 5 2016 6:9:29 with OCaml 4.02.2
olympia:vert_safety_proofs yak$ make
coqc seot_util.v
coqc analysis.v
coqc vert.v
olympia:vert_safety_proofs yak$ 
```

## About me

Work/projects: https://www.linkedin.com/in/ykouskoulas

Publications:  https://orcid.org/0000-0001-7347-7473

This repo:     https://github.com/ykouskoulas/vert_safety_proofs
