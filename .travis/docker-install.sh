#!/usr/bin/env bash

set -e

docker pull coqorg/coq:${COQ}
docker run -d -i --init --name=COQ -v ${TRAVIS_BUILD_DIR}:/home/coq/${CONTRIB_NAME} -w /home/coq/${CONTRIB_NAME} coqorg/coq:${COQ}
docker exec COQ /bin/bash --login -c "
  export PS4='+ \e[33;1m(\$0 @ line \$LINENO) \$\e[0m '; set -ex
  export OPAMYES=true
  export OPAMJOBS=2
  export OPAMVERBOSE=true
  opam update
  opam config list; opam repo list
  opam ${ELPI}
  opam list
  " install
