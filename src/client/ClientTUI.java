package client;

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
public class ClientTUI implements ClientView {
	/**
	 * The client this ClientTUI is made for.
	 */
	private Client client;
	/**
	 * The reader used to read from System.in.
	 */
	private BufferedReader reader;

	/**
	 * The InetAddress the ClientTUI will be connecting to.
	 */
	private InetAddress host;
	/**
	 * The port the ClientTUI will be connecting to.
	 */
	private int port;

	/*@	private invariant this.reader != null;
	  	private invariant client != null;
	  	private invariant host != null;
	 */

	/**
	 * Creates a ClientTUI object.
	 */
	public ClientTUI() {
		this.reader = new BufferedReader(new InputStreamReader(System.in));
	}

	/**
	 * Prints a message to System.out.
	 * 
	 * @param msg
	 *            The message to print.
	 */
	//@ requires msg != null;
	/*@ pure */@Override
	public void addMessage(String msg) {
		System.out.println(msg);
	}

	/**
	 * This method reads the messages in the InputStream. Then, it decides which
	 * command was sent, and executes this command by forwarding it to the
	 * client.
	 */
	public void readInput() {
		while (client.isAlive()) {
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
			case Client.QUIT:
				client.shutdown();
				break;
			case Client.INVITE:
				client.clientInvite(input, splitInput);
				break;
			case Client.ACCEPT_INVITE:
				client.clientAccept(input, splitInput);
				break;
			case Client.DECLINE_INVITE:
				client.clientDecline(input, splitInput);
				break;
			case Client.MOVE:
				client.clientMove(input, splitInput);
				break;
			case Client.CHAT:
				client.sendMessage(input);
				break;
			case Client.REQUEST_BOARD:
				client.clientRequestBoard();
				break;
			case Client.REQUEST_LOBBY:
				client.sendMessage(input);
				break;
			case Client.REQUEST_LEADERBOARD:
				client.sendMessage(Client.REQUEST_LEADERBOARD);
				break;
			case Client.PING:
				client.sendMessage(Client.PING);
				break;
			// CUSTOM COMMANDS
			case Client.HELP:
				client.clientHelp();
				break;
			case Client.HINT:
				client.clientHint();
				break;
			case Client.DIFFICULTY:
				client.clientDifficulty(splitInput[1]);
				break;
			// END OF CUSTOM COMMANDS
			default:
				addMessage("[ERROR]Unknown command.");
				break;
			}
		}
	}

	/**
	 * The main method to start a new ClientTUI.
	 * 
	 * @param args
	 *            The command line arguments. These aren't used.
	 */
	public static void main(String[] args) {
		new ClientTUI().setUpClient();
	}

	/**
	 * Asks the user for their name. After this, the setUpPlayer method is
	 * called.
	 */
	@Override
	public void askName() {
		while (client.isConnected() == null || !client.isConnected()) {
			if (client.isConnected() == null) {
				addMessage("Please enter your name.");
				addMessage("If you want to use a game.strategy, and make the computer play for you, use -<LETTER> <NAME>.");
				addMessage("Available strategies are: ");
				addMessage("-N for a NaiveStrategy (makes random moves)");
				addMessage("-S for Smart (thinks ahead 1 turn)");
				addMessage("-M for Minimax (thinks ahead several turns)");
				try {
					client.setUpPlayer(reader.readLine());
				} catch (IOException e) {
					addMessage("[ERROR]Input disconnected. Shutting down.");
					System.exit(0);
				}
			}
		}
		client.clientHelp();
		readInput();
	}

	/**
	 * Asks the user for the IP of the server they want to connect to.
	 * 
	 * @return The InetAddress the person wants to connect to.
	 */
	public InetAddress askHost() {
		InetAddress host = null;
		while (host == null) {
			addMessage("Please enter the IP address you'd like to connect to.");
			try {
				host = InetAddress.getByName(reader.readLine());
			} catch (UnknownHostException e) {
				addMessage("[ERROR]Unknown host.");
			} catch (IOException e) {
				addMessage("[ERROR]Input disconnected. Shutting down.");
				System.exit(0);
			}
		}
		return host;
	}

	/**
	 * Asks the user for the port of the server they want to connect to.
	 * 
	 * @return The port the person wants to connect to.
	 */
	public int askPort() {
		int port = 0;
		while (port == 0) {
			addMessage("Please enter the port you'd like to connect to.");
			try {
				port = (Integer.parseInt(reader.readLine()));
				if (!(port >= 1 & port <= 65535)) {
					addMessage("[ERROR]That is not a valid port number.");
					port = 0;
				}
			} catch (NumberFormatException e) {
				addMessage("[ERROR]That is not a valid number.");
			} catch (IOException e) {
				addMessage("[ERROR]Input disconnected. Shutting down.");
				System.exit(0);
			}
		}
		return port;
	}

	/**
	 * Creates a new client with the host and port specified.
	 */
	//@ ensures getClient() != null;
	public void setUpClient() {
		this.host = askHost();
		this.port = askPort();
		try {
			this.client = new Client(host, port, this);
		} catch (IOException e) {
			addMessage("[ERROR]Couldn't connect to the server.");
			setUpClient();
		}
		client.start();
		askName();
	}

	/**
	 * Adds a connect message to the TUI. It prefixes the message with [CONNECT]
	 * 
	 * @param message
	 *            The message to add.
	 */
	//@ requires message !=null & !message.equals("");
	/*@ pure */@Override
	public void addConnectMessage(String message) {
		addMessage("[CONNECT]" + message);
	}

	/**
	 * Adds an invite message to the TUI. It prefixes the message with [INVITE]
	 * 
	 * @param message
	 *            The message to add.
	 */
	//@ requires message !=null & !message.equals("");
	/*@ pure */@Override
	public void addInviteMessage(String message) {
		addMessage("[INVITE]" + message);
	}

	/**
	 * Adds a move message to the TUI. It prefixes the message with [MOVE]
	 * 
	 * @param message
	 *            The message to add.
	 */
	//@ requires message !=null & !message.equals("");
	/*@ pure */@Override
	public void addMoveMessage(String message) {
		addMessage(message);
	}

	/**
	 * Adds a chat message to the TUI. It prefixes the message with [CHAT]
	 * 
	 * @param message
	 *            The message to add.
	 */
	//@ requires message !=null & !message.equals("");
	/*@ pure */@Override
	public void addChatMessage(String message) {
		String[] split = message.split("\\s+");
		addMessage("[CHAT]" + split[0] + ":" + client.arrayToLine(split));
	}

	/**
	 * Adds the current board to the TUI.
	 */
	//@ requires getClient().isIngame();
	/*@ pure */@Override
	public void addBoard() {
		addMessage(client.getBoard().toString());
	}

	/**
	 * Adds a lobby message to the TUI. It prefixes the message with [LOBBY]
	 * 
	 * @param message
	 *            The message to add.
	 */
	//@ requires message !=null & !message.equals("");
	/*@ pure */@Override
	public void addLobbyMessage(String message) {
		addMessage("[LOBBY]" + message);
	}

	/**
	 * Adds a line of the leaderboard to the TUI.
	 * 
	 * @param rank
	 *            The rank this player is.
	 * @param name
	 *            The name of this player.
	 * @param wins
	 *            The amount of wins this player has.
	 * @param losses
	 *            The amount of losses this player has.
	 * @param gamesPlayed
	 *            The amount of games this player has played.
	 */
	/*@ requires !rank.equals("");
	  	requires !name.equals("");
	  	requires !wins.equals("");
	  	requires !losses.equals("");
	  	requires !gamesPlayed.equals("");
	 */
	/*@ pure */@Override
	public void addLeaderBoardLine(String rank, String name, String wins,
			String losses, String gamesPlayed) {
		addMessage(rank + ". " + name + " Wins: " + wins + " Losses: " + losses
				+ " Games played: " + gamesPlayed);

	}

	/**
	 * Adds an error message to the TUI. It prefixes the message with [ERROR]
	 * 
	 * @param message
	 *            The message to add.
	 */
	//@ requires message != null & !message.equals("");
	/*@ pure */@Override
	public void addErrorMessage(String message) {
		addMessage("[ERROR]" + message);
	}

	/**
	 * Adds a ping message to the TUI. It prefixes the message with [PING]
	 * 
	 * @param message
	 *            The message to add.
	 */
	//@ requires message != null & !message.equals("");
	/*@ pure */@Override
	public void addPingMessage(String message) {
		addMessage("[PING]" + message);
	}

	/**
	 * Adds a help message to the TUI. It prefixes the message with [HELP]
	 * 
	 * @param message
	 *            The message to add.
	 */
	//@ requires message != null & !message.equals("");
	/*@ pure */@Override
	public void addHelpMessage(String message) {
		addMessage("[HELP]" + message);
	}

	/**
	 * Adds a hint message to the TUI. It prefixes the message with [HINT]You
	 * could make a move in column:
	 * 
	 * @param move
	 *            The move to suggest.
	 */
	/*@ pure */@Override
	public void addHintMessage(int move) {
		addMessage("[HINT]You could make a move in column: " + move);
	}

	/**
	 * Adds a features message to the TUI. It prefixes the message with
	 * [FEATURES]
	 * 
	 * @param message
	 *            The message to add.
	 */
	//@ requires message != null & !message.equals("");
	/*@ pure */@Override
	public void addFeaturesMessage(String message) {
		addMessage("[FEATURES]" + message);
	}

	/**
	 * Adds a game message to the TUI. It prefixes the message with [GAME]
	 * 
	 * @param message
	 *            The message to add.
	 */
	//@ requires message != null & !message.equals("");
	/*@ pure */@Override
	public void addGameMessage(String message) {
		addMessage("[GAME]" + message);
	}

	/**
	 * Adds a difficulty message to the TUI. It prefixes the message with
	 * [DIFFICULTY]
	 * 
	 * @param success
	 *            To determine whether the difficulty was successfully switched.
	 */
	/*@ pure */@Override
	public void addDifficultyMessage(boolean success) {
		if (success) {
			addMessage("Difficulty set");
		} else {
			addMessage("Couldn't change the difficulty");
		}
	}
	
	/*@ pure */public Client getClient(){
		return client;
	}
}
