# SigmaZK

This is a standard Rocq project, which depends primarily on SSProve.
There are four options for how to install dependencies and compile the project.
After following one of the installation methods, the code files can be compiled by running
the command `make` (the `run-*.sh` scripts includes this command).
The file `compile.txt` shows the expected output of a successful compilation.

* **codespace:** To use a GitHub codespace, press the green "<> Code" button, press the "Codespaces" tab, press the "+" button.
  **NB:** Currently, Firefox seems only to partially support the VSCode browser environment.
* **opam:** For an opam based installation we suggest
    running the commands
    ```
    opam repo add coq-released https://coq.inria.fr/opam/released
    opam update
    opam pin add coq-ssprove https://github.com/SSProve/ssprove.git#9b14e90
    ```
    Alternatively, run `./run-opam.sh`.
* **nix:** For a nix based installation we suggest using the provided `shell.nix`
    by running `nix-shell` to enter an environment equipped with the required packages.
    Alternatively, run `./run-nix.sh`.
* **docker:** For a docker based installation we suggest using the provided `Dockerfile`
    to build an image with the required packages installed. Run
    ```
    docker build -t review-sigmazk .
    ```
    to build the image. Run
    ```
    docker run --rm -it review-sigmazk
    ```
    to enter the development environment.
    Alternativel, run `./run-docker.sh`.

This project takes around 5 minutes to compile. When the transitive dependencies need to be built (mathcomp, mathcomp-analysis, SSProve), they take around 30 minutes to compile.
The **codespace** and **docker** installation methods avoid building the transitive dependencies by downloading then from the mathcomp nix build cache.

See the "Artifacts" appendix in the paper for additional information.
