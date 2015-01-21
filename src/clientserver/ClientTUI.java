package clientserver;

import game.ComputerPlayer;
import game.Disc;
import game.HumanPlayer;
import game.NaiveStrategy;
import game.SmartStrategy;

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
	private Object waiter = new Object();
	private InetAddress inet;
	private int port;

	public ClientTUI(InetAddress inet, int port) {
		this.inet = inet;
		this.port = port;
		this.moveRequested = false;
		this.move = -1;
		this.reader = new BufferedReader(new InputStreamReader(System.in));
		askName();
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
				synchronized (waiter) {
					if (moveRequested) {
						moveRequested = false;
						client.sendMessage(input);
						if (splitInput.length == 2) {
							try {
								move = Integer.parseInt(splitInput[1]);
								waiter.notify();
							} catch (NumberFormatException
									| ArrayIndexOutOfBoundsException e) {
								addMessage("Please enter a valid move after MOVE.");
							}
						} else {
							addMessage("Please enter a valid move after MOVE.");
						}
					} else {
						addMessage("There was no move requested.");
					}
				}
			} else if (splitInput[0].equals("INVITE")) {
				if (splitInput.length == 1) {
					addMessage("Please add a player to invite.");
				} else if (splitInput.length == 2) {
					addMessage(splitInput[1]);
					client.addInvite(splitInput[1]);
					client.sendMessage(input);
				} else if (splitInput.length == 3) {
					addMessage("For a custom board size you need to specify both the BoardX and BoardY");
				} else if (splitInput.length >= 4) {
					try {
						client.addInvite(splitInput[1],
								Integer.parseInt(splitInput[2]),
								Integer.parseInt(splitInput[3]));
						client.sendMessage(input);
					} catch (NumberFormatException e) {
						addMessage("Please specify the BoardX and BoardY as integers.");
					}
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
		addMessage("Please enter your name (or -N for a ComputerPlayer with a NaiveStrategy or -S for a ComputerPlayer with a SmartStrategy): ");
		try {
			name = reader.readLine();
			if (name.equals("-N")) {
				name = "NaivePlayer";
				this.client = new Client(inet, port, this, new ComputerPlayer(
						Disc.YELLOW, new NaiveStrategy()));
			} else if (name.equals("-S")) {
				name = "SmartPlayer";
				this.client = new Client(inet, port, this, new ComputerPlayer(
						Disc.YELLOW, new SmartStrategy()));
			} else {
				this.client = new Client(inet, port, this, new HumanPlayer(
						Disc.YELLOW, this));
			}
		} catch (IOException e) {
			//TODO: Handle this error.
		}
		client.sendMessage(Client.CONNECT + " " + name
				+ " CUSTOM_BOARD_SIZE CHAT");
		client.setClientName(name);
		client.readInput();
	}

	public int makeMove() {
		synchronized (waiter) {
			this.move = -1;
			this.moveRequested = true;
			addMessage("Please enter a move...");
			try {
				waiter.wait();
			} catch (InterruptedException e) {
			}
			return move;
		}
	}
}
