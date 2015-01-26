package clientserver;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.PrintStream;

public class ServerTest {
	// in en out, schrijven naar uit met 2 newlines, kijken wat er gebeurt als je het uitleest
	// je hebt gewoon een out, daar schrijf je een bericht naar toe met 2 newlines. volgengens ga je daaruit lezen, en kijk je wat hij leest.
	public static void main(String[] args) throws IOException {
		PrintStream ps = new PrintStream("test.txt");
		FileInputStream input = new FileInputStream("test.txt");
		BufferedWriter out = new BufferedWriter(new OutputStreamWriter(ps));
		BufferedReader in = new BufferedReader(new InputStreamReader(input));
		out.write("lalala");
		out.newLine();
		out.newLine();
		out.flush();
		String line = in.readLine();
		while (line != null) {
			System.out.println(line);
			line = in.readLine();
		}
	}
}
