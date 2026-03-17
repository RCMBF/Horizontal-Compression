# Horizontal-Compression
This repository contains the implementation of the Horizontal-Compression Algorithm (HC) and Lean-assisted proofs about its properties.
  - The HorizontalCompression folder contains the full Lean4 project, with both the algorithm and related proofs:
    - "HorizontalCompression/Main.lean" is the proof of the main theorem (Coverage and Soundness of HC);
    - "HorizontalCompression/Example.lean" shows how to compress proofs with the Lean4 implementation of HC;
    - "HorizontalCompression/HorizontalCompression.lean" is the Lean file used to import the project's libraries.
  - "HorizontalCompressionEXEC.lean" contains the Lean4 implementation of the Horizontal-Compression Algorithm;
  - "HorizontalCompressionWEB.lean" contains the web version of the related proofs in Lean4.

To run this project, please download the contents of this repository and go to the HorizontalCompression folder.

Alternatively, you may also run this project by copying and pasting the HorizontalCompressionEXEC/WEB files to:
  - [https://live.lean-lang.org/#project=lean-nightly](https://live.lean-lang.org/#project=lean-nightly)

Note that it may take a minute or so until the file is ready.
