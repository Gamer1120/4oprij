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

/**
 * ClientTUI program for the Connect4 according to the protocol of the TI-2
 * group.<br>
 * <br>
 * Programming Project Connect4 Module 2 Softwaresystems 2014-2015 <br>
 * 
 * @author Michael Koopman s1401335 and Sven Konings s1534130
 */
public class ClientTUI extends Thread implements ClientView {
	/**
	 * The Client this ClientTUI is made for.
	 */
	private Client client;
	/**
	 * The reader used to read from System.in.
	 */
	private BufferedReader reader;
	/**
	 * A boolean to determine whether the server has requested a move.
	 */
	private boolean moveRequested;
	/**
	 * The InetAddress the ClientTUI will be connecting to.
	 */
	private InetAddress inet;
	/**
	 * The port the ClientTUI will be connecting to.
	 */
	private int port;
	/**
	 * A constant for the default adress to connect to, in this case localhost.
	 */
	private static final String DEFAULT_INET = "localhost";
	private static final int DEFAULT_PORT = 2727;

	private static final String CLIENT_FEATURES = Features.CHAT + " "
			+ Features.CUSTOM_BOARD_SIZE + " " + Features.LEADERBOARD;

	/**
	 * Creates a ClientTUI object.
	 * 
	 * @param inet
	 *            The InetAddress this ClientTUI will connect to.
	 * @param port
	 *            The port this ClientTUI will connect to.
	 */
	public ClientTUI(InetAddress inet, int port) {
		this.inet = inet;
		this.port = port;
		this.moveRequested = false;
		this.reader = new BufferedReader(new InputStreamReader(System.in));
		askName();
	}

	/**
	 * Prints a message to System.out.
	 * 
	 * @param msg
	 *            The message to print.
	 */
	public void addMessage(String msg) {
		System.out.println(msg);
	}

	/**
	 * This method reads the messages in the InputStream. Then, it decides which
	 * command was sent, and executes this command.
	 */
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
			switch (splitInput[0]) {
			case "QUIT":
				quit();
				break;
			case "HELP":
				help();
				break;
			case "MOVE":
				move(input, splitInput);
				break;
			case "INVITE":
				invite(input, splitInput);
				break;
			case "LEADERBOARD":
				client.sendMessage(Client.REQUEST_LEADERBOARD);
				break;
			case "DECLINE":
				decline(input, splitInput);
				break;
			default:
				client.sendMessage(input);
				break;
			}
		}
	}

	/**
	 * The main method to start a new ClientTUI and connect to the Server.
	 * 
	 * @param args
	 *            The command line arguments.
	 */
	public static void main(String[] args) {
		// Connects to localhost:2727
		InetAddress addr = null;
		try {
			addr = InetAddress.getByName(DEFAULT_INET);
		} catch (UnknownHostException e) {
			e.printStackTrace();
		}
		ClientTUI c = new ClientTUI(addr, DEFAULT_PORT);
		c.askName();
	}

	/**
	 * Asks the user for their name. If they enter -N or -S instead, a
	 * ComputerPlayer with a NaiveStrategy or SmartStrategy is made.
	 */
	@Override
	public void askName() {
		String name = null;
		String[] splitName = null;
		addMessage("[NAME]Please enter your name (or -N for a ComputerPlayer with a NaiveStrategy or -S for a ComputerPlayer with a SmartStrategy): ");
		try {
			name = reader.readLine();
			splitName = name.split("\\s+");
			if (splitName[0].equals("-N")) {
				if (splitName.length == 1) {
					name = "NaivePlayer";
					this.client = new Client(
							inet,
							port,
							this,
							new ComputerPlayer(Disc.YELLOW, new NaiveStrategy()));
					client.sendMessage(Client.CONNECT + " " + name + " "
							+ CLIENT_FEATURES);
				} else {
					name = splitName[1];
					this.client = new Client(
							inet,
							port,
							this,
							new ComputerPlayer(Disc.YELLOW, new NaiveStrategy()));
					client.sendMessage(Client.CONNECT + " " + name + " "
							+ CLIENT_FEATURES);
				}
			} else if (splitName[0].equals("-S")) {
				if (splitName.length == 1) {
					name = "SmartPlayer";
					this.client = new Client(
							inet,
							port,
							this,
							new ComputerPlayer(Disc.YELLOW, new SmartStrategy()));
					client.sendMessage(Client.CONNECT + " " + name + " "
							+ CLIENT_FEATURES);
				} else {
					name = splitName[1];
					this.client = new Client(
							inet,
							port,
							this,
							new ComputerPlayer(Disc.YELLOW, new SmartStrategy()));
					client.sendMessage(Client.CONNECT + " " + name + " "
							+ CLIENT_FEATURES);
				}
			} else {
				this.client = new Client(inet, port, this, new HumanPlayer(
						Disc.YELLOW, this));
				client.sendMessage(Client.CONNECT + " " + name + " "
						+ CLIENT_FEATURES);
			}
		} catch (IOException e) {
			client.shutdown();
		}

		client.setClientName(name);
		client.readInput();
	}

	/**
	 * Asks the player to make a move.
	 */
	public int makeMove() {
		this.moveRequested = true;
		addMessage("[MOVE]Please enter a move...");
		return -1;
	}

	/**
	 * Sends a Client.QUIT message to the server, and then shuts down the
	 * client.
	 */
	private void quit() {
		client.sendMessage(Client.QUIT + " Disconnected.");
		client.shutdown();
	}

	/**
	 * Shows the commands that are available. In case the client is in-game,
	 * different commands are shown than when he's not.
	 */
	private void help() {
		if (client.isIngame) {
			addMessage("[HELP]Available commands are: MOVE <column>, PING and QUIT");
		} else {
			addMessage("[HELP]Available commands are: INVITE <player>, ACCEPT <player>, DECLINE <player>, CHAT <message>, LOBBY, LEADERBOARD, PING and QUIT");
		}
	}

	/**
	 * Forwards the move the player just made to the server, if the move was
	 * valid, and there was a move requested.
	 * 
	 * @param input
	 *            The raw message the server sent.
	 * @param splitInput
	 *            The message the server sent, split up in an array.
	 */
	private void move(String input, String[] splitInput) {
		if (moveRequested) {
			moveRequested = false;
			client.sendMessage(input);
			if (splitInput.length == 2) {
				try {
					Integer.parseInt(splitInput[1]);

				} catch (NumberFormatException | ArrayIndexOutOfBoundsException e) {
					addMessage("[ERROR]Please enter a valid move after MOVE.");
				}
			} else {
				addMessage("[ERROR]Please enter a valid move after MOVE.");
			}
		} else {
			addMessage("[ERROR]There was no move requested.");

		}
	}

	/**
	 * Forwards the invite the player just made to the server, if the player
	 * added a name to invite. It saves the invite in the client. This method
	 * also supports custom board sizes.
	 * 
	 * @param input
	 *            The raw message the server sent.
	 * @param splitInput
	 *            The message the server sent, split up in an array.
	 */
	private void invite(String input, String[] splitInput) {
		if (splitInput.length == 1) {
			addMessage("[ERROR]Please add a player to invite.");
		} else if (splitInput.length == 2) {
			client.addClientInvite(splitInput[1]);
			client.sendMessage(input);
			addMessage("[INVITE]Tried to invite: " + splitInput[1]
					+ " with default board size.");
		} else if (splitInput.length == 3) {
			addMessage("[ERROR]For a custom board size you need to specify both the BoardX and BoardY");
		} else if (splitInput.length >= 4) {
			try {
				client.addClientInvite(splitInput[1],
						Integer.parseInt(splitInput[2]),
						Integer.parseInt(splitInput[3]));
				client.sendMessage(input);
				addMessage("[INVITE]Tried to invite: " + splitInput[1]
						+ " with the specified custom board size.");
			} catch (NumberFormatException e) {
				addMessage("[INVITE]Please specify the BoardX and BoardY as integers. Invite failed.");
			}
		}
	}

	/**
	 * Forwards the rejected invite to the Server, if the player specified whose
	 * invite to decline.
	 * 
	 * @param input
	 *            The raw message the server sent.
	 * @param splitInput
	 *            The message the server sent, split up in an array.
	 */
	private void decline(String input, String[] splitInput) {
		if (splitInput.length > 1) {
			client.removeServerInvite(splitInput[1]);
			client.sendMessage(input);
			addMessage("[INVITE]Tried to decline " + splitInput[1]
					+ "'s invite.");
		} else {
			addMessage("[INVITE]Please specify whose invite you'd like to decline.");
		}
	}
}
