#!/usr/bin/env python3

import argparse
import os
import json
import re


def main(args):
  ret_code = 1

  # load the test case trace records
  igen_traces = {}
  for file in os.listdir("brt-out-tmp"):
    if file.startswith("test") and file.endswith(".json"):
      with open(os.path.join("brt-out-tmp", file)) as infile:
        test = json.load(infile)
        igen_traces[file] = test['trace']

  # load the traces as reported by rply
  rply_traces = {}
  pat_test = re.compile(r"([^:]+):[^:]+:[^:]+:[^:]+:[^:]+\n")
  pat_trace = re.compile(r"([^:]+:[^:]+)\n")

  with open("output") as infile:

    test = None
    trace = []

    for line in infile:
      m = pat_test.match(line)
      if m:
        if test is not None:
          rply_traces[test] = trace
          trace = []
        test = m[1]
      m = pat_trace.match(line)
      if m:
        trace.append(m[1])

    rply_traces[test] = trace

  verified = 0;
  for test, igen_trace in igen_traces.items():
    if test not in rply_traces:
      print(test, "not found")
    else:
      rply_trace = rply_traces[test]
      if igen_trace != rply_trace:
        print(test, "trace differs")
      else:
        verified += 1

  print(verified, "of", len(igen_traces), "rply test traces verified")
  if verified == len(igen_traces):
    ret_code = 0

  return ret_code


if __name__ == "__main__":

  parser = argparse.ArgumentParser(description='validate replayed traces against original test case')
  args = parser.parse_args()
  exit(main(args))
