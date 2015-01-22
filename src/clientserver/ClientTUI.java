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
			if (input.equals("EXIT")) {
				client.shutdown();
				break;
			} else if (input.equals("HELP")) {
				if (client.isIngame) {
					addMessage("[HELP]Available commands are: MOVE <column>, PING and EXIT");
				} else {
					addMessage("[HELP]Available commands are: INVITE <player>, ACCEPT <player>, DECLINE <player>, CHAT <message>, LOBBY, LEADERBOARD, PING and EXIT");
				}
			} else if (splitInput[0].equals("MOVE")) {
				if (moveRequested) {
					moveRequested = false;
					client.sendMessage(input);
					if (splitInput.length == 2) {
						try {
							Integer.parseInt(splitInput[1]);

						} catch (NumberFormatException
								| ArrayIndexOutOfBoundsException e) {
							addMessage("[ERROR]Please enter a valid move after MOVE.");
						}
					} else {
						addMessage("[ERROR]Please enter a valid move after MOVE.");
					}
				} else {
					addMessage("[ERROR]There was no move requested.");

				}
			} else if (splitInput[0].equals("INVITE")) {
				if (splitInput.length == 1) {
					addMessage("[ERROR]Please add a player to invite.");
				} else if (splitInput.length == 2) {
					client.addClientInvite(splitInput[1]);
					client.sendMessage(input);
					addMessage("[INVITE]Successfully tried to invite: "
							+ splitInput[1] + " with default board size.");
				} else if (splitInput.length == 3) {
					addMessage("[ERROR]For a custom board size you need to specify both the BoardX and BoardY");
				} else if (splitInput.length >= 4) {
					try {
						client.addClientInvite(splitInput[1],
								Integer.parseInt(splitInput[2]),
								Integer.parseInt(splitInput[3]));
						client.sendMessage(input);
						addMessage("[INVITE]Successfully tried to invite: "
								+ splitInput[1]
								+ " with the specified custom board size.");
					} catch (NumberFormatException e) {
						addMessage("[INVITE]Please specify the BoardX and BoardY as integers. Invite failed.");
					}
				}
			} else if (splitInput[0].equals("LEADERBOARD")) {
				client.sendMessage(Client.REQUEST_LEADERBOARD);
			} else {
				client.sendMessage(input);
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
		int port = 2727;
		ClientTUI c = new ClientTUI(addr, port);
		c.askName();
	}

	/**
	 * Asks the user for their name. If they enter -N or -S instead, a
	 * ComputerPlayer with a NaiveStrategy or SmartStrategy is made.
	 */
	@Override
	public void askName() {
		String name = null;
		addMessage("[NAME]Please enter your name (or -N for a ComputerPlayer with a NaiveStrategy or -S for a ComputerPlayer with a SmartStrategy): ");
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
			client.shutdown();
		}
		client.sendMessage(Client.CONNECT + " " + name + " " + Features.CHAT
				+ " " + Features.CUSTOM_BOARD_SIZE+ " " + Features.LEADERBOARD);
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
}
