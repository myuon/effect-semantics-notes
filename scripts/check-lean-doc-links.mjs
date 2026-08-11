#!/usr/bin/env node

import { readFile, readdir } from "node:fs/promises";
import { extname, join, relative, resolve } from "node:path";

const repositoryRoot = resolve(import.meta.dirname, "..");
const declarationDataPath = resolve(
  process.argv[2] ??
    join(repositoryRoot, "formal/docbuild/.lake/build/doc/declarations/declaration-data.bmp"),
);
const ignoredDirectories = new Set([".git", ".lake", "_build", "node_modules"]);
const leanLinkPattern = /\/lean\/find\/\?pattern=([^&#)\s]+)/g;

async function markdownFiles(directory) {
  const files = [];
  for (const entry of await readdir(directory, { withFileTypes: true })) {
    if (entry.isDirectory() && ignoredDirectories.has(entry.name)) continue;
    const path = join(directory, entry.name);
    if (entry.isDirectory()) files.push(...(await markdownFiles(path)));
    else if (entry.isFile() && extname(entry.name) === ".md") files.push(path);
  }
  return files;
}

const declarationData = JSON.parse(await readFile(declarationDataPath, "utf8"));
const declarations = declarationData.declarations ?? {};
const failures = [];
let checked = 0;

for (const path of await markdownFiles(repositoryRoot)) {
  const source = await readFile(path, "utf8");
  for (const match of source.matchAll(leanLinkPattern)) {
    const pattern = decodeURIComponent(match[1].replaceAll("+", " "));
    checked += 1;
    if (Object.hasOwn(declarations, pattern)) continue;
    const line = source.slice(0, match.index).split("\n").length;
    failures.push(`${relative(repositoryRoot, path)}:${line}: ${pattern}`);
  }
}

if (failures.length > 0) {
  console.error("Broken Lean API links (declarations not found):");
  for (const failure of failures) console.error(`  ${failure}`);
  process.exitCode = 1;
} else {
  console.log(`Checked ${checked} Lean API links; every declaration exists.`);
}
