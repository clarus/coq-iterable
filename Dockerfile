FROM ubuntu
MAINTAINER Guillaume Claret

RUN apt-get update && apt-get upgrade -y
RUN apt-get install -y gcc make git

# Opam
RUN apt-get install -y opam
RUN opam init
ENV OPAMJOBS 4
RUN opam install -y coq

# Tools
RUN apt-get install -y inotify-tools

# Stable dependencies
RUN opam repo add coq https://github.com/coq/opam-coq-repo.git

# Unstable dependencies
RUN opam repo add coq-unstable https://github.com/coq/opam-coq-repo-unstable.git
RUN opam install -y coq-function-ninjas coq-monad

# Build
ADD . /root/coq-iterable
WORKDIR /root/coq-iterable
RUN eval `opam config env`; ./configure.sh && make -j

# Continuous build
CMD eval `opam config env`; ./configure.sh && while inotifywait *.v; do make; done