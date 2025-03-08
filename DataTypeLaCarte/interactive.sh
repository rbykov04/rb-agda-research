#!/bin/bash -eu

DIRECTORY_TO_OBSERVE="."      # might want to change this
function block_for_change {
  inotifywait --recursive \
    --event modify,move,create,delete \
    $DIRECTORY_TO_OBSERVE
}

function run {

  (
      make run
  ) || true
}


run
while block_for_change; do
  (
    run

  )

done
