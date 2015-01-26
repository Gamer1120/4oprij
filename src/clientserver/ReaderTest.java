package clientserver;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;

public class ReaderTest {
	// in en out, schrijven naar uit met 2 newlines, kijken wat er gebeurt als je het uitleest
	// je hebt gewoon een out, daar schrijf je een bericht naar toe met 2 newlines. volgengens ga je daaruit lezen, en kijk je wat hij leest.
	public static void main(String[] args) throws IOException {
		BufferedWriter out = new BufferedWriter(new FileWriter("test.txt"));
		BufferedReader in = new BufferedReader(new FileReader("test.txt"));
		out.write("test");
		out.newLine();
		out.newLine();
		out.write("test2");
		out.newLine();
		out.newLine();
		out.flush();
		out.close();
		while (in.ready()) {
			String line = in.readLine();
			if ("".equals(line)) {
				System.out.print("(empty)");
			} else {
				System.out.print(line);
			}
		}
		in.close();
	}
}
