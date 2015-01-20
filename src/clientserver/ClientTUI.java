package clientserver;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.net.UnknownHostException;

public class ClientTUI extends Thread implements ClientView {
	private Client client;
	private BufferedReader reader;
	private boolean moveRequested;
	private int move;

	public ClientTUI(InetAddress inet, int port) {
		this.moveRequested = false;
		this.move = -1;
		try {
			this.client = new Client(inet, port, this);
		} catch (IOException e) {
			e.printStackTrace();
		}
		this.reader = new BufferedReader(new InputStreamReader(System.in));
	}

	public void addMessage(String msg) {
		System.out.println(msg);
	}

	public void run() {
		while (true) {
			String input = null;
			String[] splitInput = null;
			try {
				input = reader.readLine();
				splitInput = input.split("\\s+");
			} catch (IOException | NullPointerException e) {
				client.shutdown();
				break;
			}
			if (input.equals("EXIT")) {
				client.shutdown();
				break;
			} else if (splitInput[0].equals("MOVE")) {
				if (moveRequested) {
					moveRequested = false;
					client.sendMessage(input);
					if (splitInput.length == 2) {
						try {
							move = Integer.parseInt(splitInput[1]);
						} catch (NumberFormatException
								| ArrayIndexOutOfBoundsException e) {
							addMessage("Please enter a valid move after MOVE.");
						}
					} else {
						addMessage("Please enter a valid move after MOVE.");
					}
				} else {
					addMessage("There was move requested.");
				}
			} else {
				client.sendMessage(input);
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

	public int makeMove() {
		this.move = -1;
		this.moveRequested = true;
		addMessage("Please enter a move...");
		while (move == -1) {
		}
		return move;
	}
}
