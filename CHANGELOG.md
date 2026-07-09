# Revision history for coo

## 0.1.0.0 -- 2026-06-10

* First version. Basic functionality of the dynamic runtime system, including:

  - An interactive REPL with participates *inside* the flow of control.

  - Full polarization correction, with automatic shift insertion to give a
    call-by-value look and feel.

  - Translation into a small dual core based on the sequent calculus.

  - A general abstract machine for running sequent calculus programs.

  - Optional simple type inference/checking for both the source language and
    dual core intermediate language.
