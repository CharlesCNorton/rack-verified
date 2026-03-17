# RACK DeepSpec CI image
#
# Provides Rocq 9.0 + VST + CompCert + ITree for the deepspec CI job.
# The deepspec job in .github/workflows/build.yml uses this image via:
#   custom_image: ghcr.io/charlescnorton/rack-deepspec:latest
#
# Build:
#   docker build -t ghcr.io/charlescnorton/rack-deepspec:latest deepspec/
#
# Push (requires GHCR auth):
#   echo $GITHUB_TOKEN | docker login ghcr.io -u charlescnorton --password-stdin
#   docker push ghcr.io/charlescnorton/rack-deepspec:latest
#
# Rebuild when VST, CompCert, or ITree versions change.

FROM rocq/rocq-prover:9.0-ocaml-4.14-flambda

LABEL org.opencontainers.image.source=https://github.com/CharlesCNorton/rack-verified
LABEL org.opencontainers.image.description="RACK DeepSpec CI: Rocq 9.0 + VST 2.16 + CompCert 3.16 + ITree 5.2.1"

RUN opam update -y && opam install coq-vst.2.16 coq-compcert.3.16 coq-itree.5.2.1 -y -j2
