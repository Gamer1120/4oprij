package clientserver;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.net.UnknownHostException;

public class ClientTUI extends Thread implements ClientView {
	private Client client;
	private BufferedReader reader;

	public ClientTUI(InetAddress inet, int port) {
		try {
			this.client = new Client(inet, port, this);
		} catch (IOException e) {
			e.printStackTrace();
		}
		this.reader = new BufferedReader(new InputStreamReader(
				System.in));
	}

	public void addMessage(String msg) {
		System.out.println(msg);
	}

	public void run() {
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
		ClientTUI c = new ClientTUI(addr, port);
		c.askName();
	}

	@Override
	public void askName() {
		String name = null;
		try {
			name = reader.readLine();
		} catch (IOException e) {
			client.shutdown();
		}
		client.sendMessage(Client.CONNECT + " " + name);
		client.readInput();
	}
}
