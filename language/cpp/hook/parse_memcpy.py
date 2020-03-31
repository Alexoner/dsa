import mmap
import re
import json
import functools

def shortname(cppfullname):
    pattern = re.compile("(.*?::)*(.*)[(].*[)]")
    result = pattern.match(cppfullname)
    ret = cppfullname if result is None else result.group(2) + "()" if result.group(1) is None else result.group(1) + result.group(2) + "()"
    return ret

class CallStat:
    def __init__(self, name, level):
        self.name = name
        self.level = level
        self.num_calls = 0
        self.num_size = 0
        self.callers = {}

    def add(self, size, callstack):
        self.num_calls += 1
        self.num_size += size
        if self.level < len(callstack):
            callername = callstack[self.level - 1 + 1]
            if not callername in self.callers: self.callers[callername] = CallStat(callername, self.level + 1)
            self.callers[callername].add(size, callstack)

    def dump(self, usemap = False):
        #list(functools.reduce(lambda x: x.dump(), self.callers.values()))
        callers = {} if usemap else []
        if usemap:
            for key, value in self.callers.items():
                #shortname not working.. maybe samename with overloads?
                #callers[shortname(key)] = value.dump(usemap)
                callers[key] = value.dump(usemap)
        else:
            for value in self.callers.values():
                callers.append(value.dump(usemap))
        return { "name": self.name, "level": self.level, "num_calls": self.num_calls, "num_size": self.num_size, "_callers": callers }


class StackTraceParser:
    pattern = "memcpy size[:] ([0-9]+) backtrace[:]\n((?:[ 0-9]+[#] .* in .*\n)+)"
    regex = re.compile(pattern, re.MULTILINE)
    utf8regex = re.compile(pattern.encode("utf-8"))
    functionre = re.compile("[ 0-9]+[#] (.*) in .*")
    name_to_match = "__wrap_memcpy"

    @staticmethod
    def ParseCallstack(stack, maxdepth):
        frames = stack.split("\n")
        ret = []
        depth = 0
        for frame in frames:
            match = StackTraceParser.functionre.search(frame)
            if match is None: break
            ret.append(match.group(1))
            depth += 1
            if depth == maxdepth: break
        return ret

    @staticmethod
    def ParseLog(s, maxdepth = 0, regex = None):
        stat = CallStat(StackTraceParser.name_to_match, 0)
        if regex == None: regex = StackTraceParser.regex
        for stack in regex.findall(s):
            frames = stack[1] if stack[1] is str else stack[1].decode("utf-8")
            frames = StackTraceParser.ParseCallstack(frames, maxdepth)
            if frames[0] != StackTraceParser.name_to_match: continue
            size = int(stack[0])
            stat.add(size, frames[1:])
        return stat

    @staticmethod
    def ParseFile(path, maxdepth = 0):
        with open(path, 'r', encoding="utf-8") as f:
            with mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ) as m:
                return StackTraceParser.ParseLog(m, maxdepth, StackTraceParser.utf8regex)


p = StackTraceParser()
stat = p.ParseFile('onelog.txt')
output = open('output.txt', 'w')
print(stat.dump(), file=output)
output.close()
