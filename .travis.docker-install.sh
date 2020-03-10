#!/usr/bin/env bash

docker pull ${COQ}
docker run -d -i --init --name=COQ -v ${TRAVIS_BUILD_DIR}:/home/coq/${CONTRIB_NAME} -w /home/coq/${CONTRIB_NAME} ${COQ}
docker exec COQ /bin/bash --login -c "
  export PS4='+ \e[33;1m(\$0 @ line \$LINENO) \$\e[0m '; set -ex
  opam update -y
  opam install -y -v -j ${NJOBS} ${ELPI}
  opam config list; opam repo list; opam list
  " install
