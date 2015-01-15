package clientserver;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.net.UnknownHostException;

public class ClientTUI implements MessageUI {
	private Client client;

	public ClientTUI(String name, InetAddress inet, int port) {
		try {
			this.client = new Client(name, inet, port, this);
			client.start();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public void addMessage(String msg) {
		System.out.println(msg);
	}

	public void readInput() {
		BufferedReader reader = new BufferedReader(new InputStreamReader(
				System.in));
		while (true) {
			try {
				String input = reader.readLine();
				if (input.equals("EXIT")) {
					client.shutdown();
				}
				client.sendMessage(input);
			} catch (IOException e) {
				client.shutdown();
			}
		}
	}

	public static void main(String[] args) {
		// Connects to localhost:2727
		InetAddress addr = null;
		try {
			addr = InetAddress.getByName("localhost");
		} catch (UnknownHostException e) {
			e.printStackTrace();
		}
		int port = 2727;
		ClientTUI c = new ClientTUI("Michael", addr, port);
		c.readInput();
	}
}
