# Xena Project 2020

This repository formalises the topological concepts of polygonal-connectedness in complex numbers and path-connectedness as part of the Xena Summer Projects 2020 under Prof Kevin Buzzard.

## polygonal_connectedness.lean

### Definitions

- Polygonally-connected and step-connected (polygonally-connected using only horizontal and vertical line segments) pairs of complex numbers
- Polygonally-connected and step-connected subsets of ℂ
- Regions (a.k.a. domains) in topological spaces

### Main Theorems

- Step-connectedness implies polygonal-connectedness
- All regions in ℂ are step-connected

## path_connectedness.lean

### Definitions

- Path-connectedned points of a topological space
- Path components and path-connected subsets of a space
- Path-connected spaces

### Main Theorems

- Pointwise path-connectedness is an equivalence relation
- Path-connectedness implies connectedness but not vice-versa (deleted comb space)

### Side-lemmas

- Connectedness of a dense subset implies that of the entire set
- Continuity on restricted domains
- An alternate characterisation of connectedness using continuous functions to a discrete two-space
