/*
 * [The "BSD license"]
 *  Copyright (c) 2012 Terence Parr
 *  Copyright (c) 2012 Sam Harwell
 *  All rights reserved.
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 *  1. Redistributions of source code must retain the above copyright
 *     notice, this list of conditions and the following disclaimer.
 *  2. Redistributions in binary form must reproduce the above copyright
 *     notice, this list of conditions and the following disclaimer in the
 *     documentation and/or other materials provided with the distribution.
 *  3. The name of the author may not be used to endorse or promote products
 *     derived from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 *  IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 *  OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 *  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 *  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 *  NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 *  THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
package org.antlr.v4.test.runtime.go;

import org.antlr.v4.Tool;
import org.antlr.v4.automata.ATNFactory;
import org.antlr.v4.automata.ATNPrinter;
import org.antlr.v4.automata.LexerATNFactory;
import org.antlr.v4.automata.ParserATNFactory;
import org.antlr.v4.codegen.CodeGenerator;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonToken;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.IntStream;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.RuleContext;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenSource;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.WritableToken;
import org.antlr.v4.runtime.atn.ATN;
import org.antlr.v4.runtime.atn.ATNDeserializer;
import org.antlr.v4.runtime.atn.ATNSerializer;
import org.antlr.v4.runtime.atn.ATNState;
import org.antlr.v4.runtime.atn.LexerATNSimulator;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.misc.IntegerList;
import org.antlr.v4.runtime.misc.Interval;
import org.antlr.v4.semantics.SemanticPipeline;
import org.antlr.v4.test.runtime.java.ErrorQueue;
import org.antlr.v4.tool.ANTLRMessage;
import org.antlr.v4.tool.DOTGenerator;
import org.antlr.v4.tool.DefaultToolListener;
import org.antlr.v4.tool.Grammar;
import org.antlr.v4.tool.GrammarSemanticsMessage;
import org.antlr.v4.tool.LexerGrammar;
import org.antlr.v4.tool.Rule;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.rules.TestRule;
import org.junit.rules.TestWatcher;
import org.junit.rules.Timeout;
import org.junit.runner.Description;
import org.stringtemplate.v4.ST;
import org.stringtemplate.v4.STGroup;
import org.stringtemplate.v4.STGroupString;

import java.io.*;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

public abstract class BaseTest {
	// -J-Dorg.antlr.v4.test.BaseTest.level=FINE
	// private static final Logger LOGGER =
	// Logger.getLogger(BaseTest.class.getName());

	public File tmpdir = null;
	public File parserpkgdir = null; // this is where the parser package is stored, typically inside the tmpdir
	private static File runtimeTmpDir = null;
	private static final String GO_RUNTIME_IMPORT_PATH = "github.com/pboyer/antlr4/runtime/Go/antlr"; // TODO: Change this before merging with upstream

	/**
	 * If error during parser execution, store stderr here; can't return stdout
	 * and stderr. This doesn't trap errors from running antlr.
	 */
	protected String stderrDuringParse;

	@org.junit.Rule
	public final TestRule testWatcher = new TestWatcher() {

		@Override
		protected void succeeded(Description description) {
			// remove tmpdir if no error.
			eraseTempDir();
		}

	};

	@org.junit.Rule
	public final Timeout eachTimeout = new Timeout(60000);

	/**
	 * Copies all files from go runtime to a temporary folder that is inside a valid GOPATH project structure.
	 * Recursively sets deleteOnExit on all temporary files and directories.
	 */
	@BeforeClass
	public static void setupGoRuntime() throws Exception {
		runtimeTmpDir = new File(System.getProperty("java.io.tmpdir"), "antlr-goruntime-tmpgopath-"
				+ Long.toHexString(System.nanoTime()));

		if (!runtimeTmpDir.mkdir()) {
			throw new Exception("Could not create temp directory for Go runtime: " + runtimeTmpDir);
		}
		runtimeTmpDir.deleteOnExit();

		ArrayList<String> pathsegments = new ArrayList<String>();
		pathsegments.add("src");
		pathsegments.addAll(Arrays.asList(GO_RUNTIME_IMPORT_PATH.split("/")));

		File tmpPackageDir = runtimeTmpDir;
		for (String pathsegment : pathsegments) {
			tmpPackageDir = new File(tmpPackageDir, pathsegment);
			if (!tmpPackageDir.mkdir()) {
				throw new Exception("Could not create temp directory for Go runtime: " + tmpPackageDir);
			}
			tmpPackageDir.deleteOnExit();
		}

		File[] runtimeFiles = locateRuntime().listFiles();
		if (runtimeFiles == null) {
			throw new Exception("Go runtime file list is empty.");
		}
		for (File runtimeFile : runtimeFiles) {
			File dest = new File(tmpPackageDir, runtimeFile.getName());
			copyFile(runtimeFile, dest);
			dest.deleteOnExit();
		}
	}

	private static void copyFile(File source, File dest) throws IOException {
		InputStream is = new FileInputStream(source);
		OutputStream os = new FileOutputStream(dest);
		byte[] buf = new byte[4 << 10];
		int l;
		while ((l = is.read(buf)) > -1) {
			os.write(buf, 0, l);
		}
		is.close();
		os.close();
	}

	@Before
	public void setUp() throws Exception {
		// new output dir for each test
		String prop = System.getProperty("antlr-go-test-dir");
		if (prop != null && prop.length() > 0)
			tmpdir = new File(prop);
		else
			tmpdir = new File(System.getProperty("java.io.tmpdir"),
					getClass().getSimpleName() + "-" + System.currentTimeMillis());

		if (tmpdir.exists())
			this.eraseFiles(tmpdir);

		parserpkgdir = new File(tmpdir, "parser");

		if (parserpkgdir.exists()) {
			this.eraseFiles(parserpkgdir);
		}
	}

	private org.antlr.v4.Tool newTool(String[] args) {
		return new Tool(args);
	}

	protected ATN createATN(Grammar g, boolean useSerializer) {
		if (g.atn == null) {
			semanticProcess(g);
			assertEquals(0, g.tool.getNumErrors());

			ParserATNFactory f;
			if (g.isLexer()) {
				f = new LexerATNFactory((LexerGrammar) g);
			} else {
				f = new ParserATNFactory(g);
			}

			g.atn = f.createATN();
			assertEquals(0, g.tool.getNumErrors());
		}

		ATN atn = g.atn;
		if (useSerializer) {
			char[] serialized = ATNSerializer.getSerializedAsChars(atn);
			return new ATNDeserializer().deserialize(serialized);
		}

		return atn;
	}

	private void semanticProcess(Grammar g) {
		if (g.ast != null && !g.ast.hasErrors) {
			System.out.println(g.ast.toStringTree());
			Tool antlr = new Tool();
			SemanticPipeline sem = new SemanticPipeline(g);
			sem.process();
			if (g.getImportedGrammars() != null) { // process imported grammars
													// (if any)
				for (Grammar imp : g.getImportedGrammars()) {
					antlr.processNonCombinedGrammar(imp, false);
				}
			}
		}
	}

	/** Return true if all is ok, no errors */
	protected ErrorQueue antlr(String fileName, String grammarFileName,
			String grammarStr, boolean defaultListener, String... extraOptions) {
		if(grammarStr!=null) {
			System.out.println("dir " + parserpkgdir);
			mkdir(parserpkgdir);
			writeFile(parserpkgdir, fileName, grammarStr);
		}
		final List<String> options = new ArrayList<String>();
		Collections.addAll(options, extraOptions);
		options.add("-Dlanguage=Go");
		options.add("-o");
		options.add(parserpkgdir.getPath());
		options.add("-lib");
		options.add(parserpkgdir.getPath());
		options.add(new File(parserpkgdir, grammarFileName).getPath());

		final String[] optionsA = new String[options.size()];
		options.toArray(optionsA);
		Tool antlr = newTool(optionsA);
		ErrorQueue equeue = new ErrorQueue(antlr);
		antlr.addListener(equeue);
		if (defaultListener) {
			antlr.addListener(new DefaultToolListener(antlr));
		}
		antlr.processGrammarsOnCommandLine();

		if (!defaultListener && !equeue.errors.isEmpty()) {
			System.err.println("antlr reports errors from " + options);
			for (int i = 0; i < equeue.errors.size(); i++) {
				ANTLRMessage msg = equeue.errors.get(i);
				System.err.println(msg);
			}
			System.out.println("!!!\ngrammar:");
			System.out.println(grammarStr);
			System.out.println("###");
		}
		if (!defaultListener && !equeue.warnings.isEmpty()) {
			System.err.println("antlr reports warnings from " + options);
			for (int i = 0; i < equeue.warnings.size(); i++) {
				ANTLRMessage msg = equeue.warnings.get(i);
				System.err.println(msg);
			}
		}

		return equeue;
	}

	protected String execLexer(String grammarFileName, String grammarStr,
			String lexerName, String input) {
		return execLexer(grammarFileName, grammarStr, lexerName, input, false);
	}

	protected String execLexer(String grammarFileName, String grammarStr,
			String lexerName, String input, boolean showDFA) {
		boolean success = rawGenerateAndBuildRecognizer(grammarFileName,
				grammarStr, null, lexerName, "-no-listener");
		assertTrue(success);
		writeFile(tmpdir, "input", input);
		writeLexerTestFile(lexerName, showDFA);
		String output = execModule("Test.go");
		if (stderrDuringParse != null && stderrDuringParse.length() > 0) {
			System.err.println(stderrDuringParse);
		}
		return output;
	}

	protected String execParser(String grammarFileName, String grammarStr,
			String parserName, String lexerName, String listenerName,
			String visitorName, String startRuleName, String input,
			boolean debug) {
		boolean success = rawGenerateAndBuildRecognizer(grammarFileName,
				grammarStr, parserName, lexerName, "-visitor");
		assertTrue(success);
		writeFile(tmpdir, "input", input);
		rawBuildRecognizerTestFile(parserName, lexerName, listenerName,
				visitorName, startRuleName, debug);
		return execRecognizer();
	}

	/** Return true if all is well */
	protected boolean rawGenerateAndBuildRecognizer(String grammarFileName,
			String grammarStr, String parserName, String lexerName,
			String... extraOptions) {
		return rawGenerateAndBuildRecognizer(grammarFileName, grammarStr,
				parserName, lexerName, false, extraOptions);
	}

	/** Return true if all is well */
	protected boolean rawGenerateAndBuildRecognizer(String grammarFileName,
			String grammarStr, String parserName, String lexerName,
			boolean defaultListener, String... extraOptions) {
		antlr(grammarFileName, grammarFileName, grammarStr, defaultListener, extraOptions);

		return true; // allIsWell: no compile
	}

	private void rawBuildRecognizerTestFile(String parserName,
											String lexerName, String listenerName, String visitorName,
											String parserStartRuleName, boolean debug) {
		this.stderrDuringParse = null;
		if (parserName == null) {
			writeLexerTestFile(lexerName, false);
		} else {
			writeParserTestFile(parserName, lexerName, listenerName,
					visitorName, parserStartRuleName, debug);
		}
	}

	private String execRecognizer() {
		return execModule("Test.go");
	}

	private String execModule(String fileName) {
		String goExecutable = locateGo();
		String modulePath = new File(tmpdir, fileName).getAbsolutePath();
		String inputPath = new File(tmpdir, "input").getAbsolutePath();
		try {
			ProcessBuilder builder = new ProcessBuilder(goExecutable, "run", modulePath, inputPath);
			String gopath = runtimeTmpDir.getPath();
			String gopathOriginal = builder.environment().get("GOPATH");
			if (gopathOriginal != null && gopathOriginal.length() > 0) {
				gopath = gopath + File.pathSeparatorChar + gopathOriginal;
			}
			builder.environment().put("GOPATH", gopath);
			builder.directory(tmpdir);
			Process process = builder.start();
			StreamVacuum stdoutVacuum = new StreamVacuum(process.getInputStream());
			StreamVacuum stderrVacuum = new StreamVacuum(process.getErrorStream());
			stdoutVacuum.start();
			stderrVacuum.start();
			process.waitFor();
			stdoutVacuum.join();
			stderrVacuum.join();
			String output = stdoutVacuum.toString();
			if (stderrVacuum.toString().length() > 0) {
				this.stderrDuringParse = stderrVacuum.toString();
				System.err.println("exec stderrVacuum: " + stderrVacuum);
			}
			return output;
		}
		catch (Exception e) {
			System.err.println("can't exec recognizer");
			e.printStackTrace(System.err);
		}
		return null;
	}

	private String locateTool(String tool) {
		ArrayList<String> paths = new ArrayList<String>(); // default cap is about right

		// GOROOT should have priority if set
		String goroot = System.getenv("GOROOT");
		if (goroot != null) {
			paths.add(goroot + File.separatorChar + "bin");
		}

		String pathEnv = System.getenv("PATH");
		if (pathEnv != null) {
			paths.addAll(Arrays.asList(pathEnv.split(File.pathSeparator)));
		}

		// OS specific default locations of binary dist as last resort
		paths.add("/usr/local/go/bin");
		paths.add("c:\\Go\\bin");

		for (String path : paths) {
			File candidate = new File(new File(path), tool);
			if (candidate.exists()) {
				return candidate.getPath();
			}
		}
		return null;
	}

	private String locateGo() {
		String propName = "antlr-go";
		String prop = System.getProperty(propName);
		if (prop == null || prop.length() == 0) {
			prop = locateTool("go");
		}
		if (prop == null) {
			throw new RuntimeException("Missing system property:" + propName);
		}
		return prop;
	}

	private static File locateRuntime() {
		final ClassLoader loader = Thread.currentThread().getContextClassLoader();
		final URL runtimeSrc = loader.getResource("Go");
		if ( runtimeSrc==null ) {
			throw new RuntimeException("Cannot find Go ANTLR runtime");
		}
		File runtimeDir = new File(runtimeSrc.getPath(), "antlr");
		if (!runtimeDir.exists()) {
			throw new RuntimeException("Cannot find Go ANTLR runtime");
		}
		return runtimeDir;
	}

	public void testErrors(String[] pairs, boolean printTree) {
		for (int i = 0; i < pairs.length; i += 2) {
			String input = pairs[i];
			String expect = pairs[i + 1];

			String[] lines = input.split("\n");
			String fileName = getFilenameFromFirstLineOfGrammar(lines[0]);
			ErrorQueue equeue = antlr(fileName, fileName, input, false);

			String actual = equeue.toString(true);
			actual = actual.replace(tmpdir + File.separator, "");
			System.err.println(actual);
			String msg = input;
			msg = msg.replace("\n", "\\n");
			msg = msg.replace("\r", "\\r");
			msg = msg.replace("\t", "\\t");

			assertEquals("error in: " + msg, expect, actual);
		}
	}

	private String getFilenameFromFirstLineOfGrammar(String line) {
		String fileName = "A" + Tool.GRAMMAR_EXTENSION;
		int grIndex = line.lastIndexOf("grammar");
		int semi = line.lastIndexOf(';');
		if (grIndex >= 0 && semi >= 0) {
			int space = line.indexOf(' ', grIndex);
			fileName = line.substring(space + 1, semi) + Tool.GRAMMAR_EXTENSION;
		}
		if (fileName.length() == Tool.GRAMMAR_EXTENSION.length())
			fileName = "A" + Tool.GRAMMAR_EXTENSION;
		return fileName;
	}

	private static class StreamVacuum implements Runnable {
		StringBuilder buf = new StringBuilder();
		BufferedReader in;
		Thread sucker;

		StreamVacuum(InputStream in) {
			this.in = new BufferedReader(new InputStreamReader(in));
		}

		public void start() {
			sucker = new Thread(this);
			sucker.start();
		}

		@Override
		public void run() {
			try {
				String line = in.readLine();
				while (line != null) {
					buf.append(line);
					buf.append('\n');
					line = in.readLine();
				}
			} catch (IOException ioe) {
				System.err.println("can't read output from process");
			}
		}

		/** wait for the thread to finish */
		void join() throws InterruptedException {
			sucker.join();
		}

		@Override
		public String toString() {
			return buf.toString();
		}
	}

	public static void writeFile(File dir, String fileName, String content) {
		try {
			File f = new File(dir, fileName);
			FileWriter w = new FileWriter(f);
			BufferedWriter bw = new BufferedWriter(w);
			bw.write(content);
			bw.close();
			w.close();
		} catch (IOException ioe) {
			System.err.println("can't write file");
			ioe.printStackTrace(System.err);
		}
	}

	public static void writeFile(String dir, String fileName, InputStream content) {
		try {
			File f = new File(dir, fileName);
			OutputStream output = new FileOutputStream(f);
			while(content.available()>0) {
				int b = content.read();
				output.write(b);
			}
			output.close();
		} catch (IOException ioe) {
			System.err.println("can't write file");
			ioe.printStackTrace(System.err);
		}
	}

	protected void mkdir(File dir) {
		dir.mkdirs();
	}

	private void writeParserTestFile(String parserName, String lexerName,
									 String listenerName, String visitorName,
									 String parserStartRuleName, boolean debug) {
			ST outputFileST = new ST(
					"package main\n" +
						"import (\n"
						+"	\"github.com/pboyer/antlr4/runtime/Go/antlr\"\n"
						+"	\"./parser\"\n"
						+"	\"os\"\n"
						+")\n"
						+ "\n"
						+ "type TreeShapeListener struct {\n"
						+ "	*parser.Base<listenerName>\n"
						+ "}\n"
						+ "\n"
						+ "func NewTreeShapeListener() *TreeShapeListener {\n"
						+ "	return new(TreeShapeListener)\n"
						+ "}\n"
						+ "\n"
						+ "func (this *TreeShapeListener) EnterEveryRule(ctx antlr.ParserRuleContext) {\n"
						+ "	for i := 0; i\\<ctx.GetChildCount(); i++ {\n"
						+ "		child := ctx.GetChild(i)\n"
						+ "		parentR,ok := child.GetParent().(antlr.RuleNode)\n"
						+ "		if !ok || parentR.GetBaseRuleContext() != ctx.GetBaseRuleContext() {\n"
						+ "			panic(\"Invalid parse tree shape detected.\")\n"
						+ "		}\n"
						+ "	}\n"
						+ "}\n"
						+ "\n"
						+ "func main() {\n"
						+ "	input := antlr.NewFileStream(os.Args[1])\n"
						+ "	lexer := parser.New<lexerName>(input)\n"
						+ "	stream := antlr.NewCommonTokenStream(lexer,0)\n"
						+ "<createParser>"
						+ "	p.BuildParseTrees = true\n"
						+ "	tree := p.<parserStartRuleName>()\n"
						+ "	antlr.ParseTreeWalkerDefault.Walk(NewTreeShapeListener(), tree)\n"
						+ "}\n");

		ST createParserST = new ST(
				"	p := parser.New<parserName>(stream)\n");
		if (debug) {
			createParserST = new ST(
					"	p := parser.New<parserName>(stream)\n"
							+ "	p.AddErrorListener(antlr.NewDiagnosticErrorListener(true))\n");
		}
		outputFileST.add("createParser", createParserST);
		outputFileST.add("parserName", parserName);
		outputFileST.add("lexerName", lexerName);
		outputFileST.add("listenerName", listenerName);
		outputFileST.add("visitorName", visitorName);
		outputFileST.add("parserStartRuleName", parserStartRuleName.substring(0, 1).toUpperCase() + parserStartRuleName.substring(1) );
		writeFile(tmpdir, "Test.go", outputFileST.render());
	}


	private void writeLexerTestFile(String lexerName, boolean showDFA) {
		ST outputFileST = new ST(
				"package main\n" +
				"import (\n"
					+ "	\"github.com/pboyer/antlr4/runtime/Go/antlr\"\n"
					+ "	\"./parser\"\n"
					+ "	\"os\"\n"
					+ "	\"fmt\"\n"
					+ ")\n"
					+ "\n"
					+ "func main() {\n"
					+ "	input := antlr.NewFileStream(os.Args[1])\n"
					+ "	lexer := parser.New<lexerName>(input)\n"
					+ "	stream := antlr.NewCommonTokenStream(lexer,0)\n"
					+ "	stream.Fill()\n"
					+ "	for _, t := range stream.GetAllTokens() {\n"
					+ "		fmt.Println(t)\n"
					+ "	}\n"
					+ (showDFA ? "fmt.Print(lexer.GetInterpreter().DecisionToDFA[antlr.LexerDefaultMode].ToLexerString())\n"
							: "")
					+ "}\n"
					+ "\n");
		outputFileST.add("lexerName", lexerName);
		writeFile(tmpdir, "Test.go", outputFileST.render());
	}

	private void eraseFiles(File dir) {
		File[] files = dir.listFiles();
		if (files == null) {
			return;
		}
		for (File file : files) {
			file.delete();
		}
	}

	private void eraseTempDir() {
		boolean doErase = true;
		String propName = "antlr-go-erase-test-dir";
		String prop = System.getProperty(propName);
		if (prop != null && prop.length() > 0)
			doErase = Boolean.getBoolean(prop);
		if (doErase) {
			if (tmpdir.exists()) {
				eraseFiles(tmpdir);
				tmpdir.delete();
			}
		}
	}

	public List<String> realElements(List<String> elements) {
		return elements.subList(Token.MIN_USER_TOKEN_TYPE, elements.size());
	}

	/** Sort a list */
	public <T extends Comparable<? super T>> List<T> sort(List<T> data) {
		List<T> dup = new ArrayList<T>();
		dup.addAll(data);
		Collections.sort(dup);
		return dup;
	}

	/** Return map sorted by key */
	public <K extends Comparable<? super K>, V> LinkedHashMap<K, V> sort(
			Map<K, V> data) {
		LinkedHashMap<K, V> dup = new LinkedHashMap<K, V>();
		List<K> keys = new ArrayList<K>();
		keys.addAll(data.keySet());
		Collections.sort(keys);
		for (K k : keys) {
			dup.put(k, data.get(k));
		}
		return dup;
	}
}
