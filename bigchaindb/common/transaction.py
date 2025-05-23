# Copyright © 2020 Interplanetary Database Association e.V.,
# BigchainDB and IPDB software contributors.
# SPDX-License-Identifier: (Apache-2.0 AND CC-BY-4.0)
# Code is Apache-2.0 and docs are CC-BY-4.0

"""Transaction related models to parse and construct transaction
payloads.

Attributes:
    UnspentOutput (namedtuple): Object holding the information
        representing an unspent output.

"""
import json
import os
from datetime import datetime

from collections import namedtuple
from copy import deepcopy
from functools import reduce, lru_cache
import rapidjson
from datetime import datetime
from subprocess import Popen, PIPE
####

from pyshacl import validate
from rdflib import Graph, Namespace, Literal, RDF, URIRef, XSD

from rdflib import plugin
from rdflib.serializer import Serializer


import os
import json
import logging
import time


#from SPARQLWrapper import SPARQLWrapper
####
import base58
import logging
from cryptoconditions import Fulfillment, ThresholdSha256, Ed25519Sha256
from cryptoconditions.exceptions import (
    ParsingError,
    ASN1DecodeError,
    ASN1EncodeError,
    UnsupportedTypeError,
)
from bigchaindb_driver.crypto import generate_keypair

try:
    from hashlib import sha3_256
except ImportError:
    from sha3 import sha3_256

from bigchaindb.common import config
from bigchaindb.common.crypto import PrivateKey, hash_data
from bigchaindb.common.exceptions import (
    AmountError,
    AssetIdMismatch,
    DoubleSpend,
    InputDoesNotExist,
    InsufficientCapabilities,
    InvalidHash,
    InvalidSignature,
    KeypairMismatchException,
    DuplicateTransaction,
    ThresholdTooDeep,
    ValidationError,
    InvalidAccount,
)
from bigchaindb.common.utils import serialize
from .memoize import memoize_from_dict, memoize_to_dict
from functools import lru_cache


logger = logging.getLogger(__name__)

UnspentOutput = namedtuple(
    "UnspentOutput",
    (
        # TODO 'utxo_hash': sha3_256(f'{txid}{output_index}'.encode())
        # 'utxo_hash',   # noqa
        "transaction_id",
        "output_index",
        "amount",
        "asset_id",
        "condition_uri",
    ),
)



import time
import json
import logging
from rdflib import Graph
from functools import lru_cache
from pyshacl import validate

# Set up logging
log_file = 'transaction_validation.log'
logging.basicConfig(level=logging.DEBUG, filename=log_file, 
                    format='%(asctime)s - %(levelname)s - %(message)s')

# Static context (common across all transaction types)
STATIC_CONTEXT = {
    "@context": {
        "ex": "http://example.org/",
        "schema": "http://schema.org/"
    }
}

# Base properties common to all transactions
BASE_PROPERTIES = {
    "transaction_id": {"rdf_property": "ex:transaction_id"},
    "operation": {"rdf_property": "ex:operation"}
}

# Transaction types configuration, with common properties extracted
transaction_config = {
    "BUYOFFER": {
        "properties": {
            **BASE_PROPERTIES,
            "adv_ref": {
                "rdf_property": "ex:adv_ref",
                "base": "http://example.org/txn/",
                "shape": "ex:AdvShape"
            },
            "asset_ref": {
                "rdf_property": "ex:asset_ref",
                "base": "http://example.org/txn/", 
                "shape": "ex:AssetShape"
            },
            "spend": {
                "rdf_property": "ex:spend",
                "base": "http://example.org/txn/", 
                "shape": "ex:AssetShape"
            }
        }
    },
    "SELL": {
        "properties": {
            **BASE_PROPERTIES,
            "adv_ref": {
                "rdf_property": "ex:adv_ref",
                "base": "http://example.org/txn/",
                "shape": "ex:AdvShape"
            },
            "buyOffer_ref": {
                "rdf_property": "ex:buyOffer_ref",
                "base": "http://example.org/txn/",
                "shape": "ex:BuyOfferShape"
            },
            "spend": {
                "rdf_property": "ex:spend",
                "base": "http://example.org/txn/", 
                "shape": "ex:AssetShape"
            }
        }
    },
    "REQUEST_RETURN": {
            "properties": {
                **BASE_PROPERTIES,
                "sell_ref": {
                    "rdf_property": "ex:sell_ref",
                    "base": "http://example.org/txn/",
                    #"shape": "ex:SellShape"
                },
                # "asset_ref": {
                #     "rdf_property": "ex:asset_ref",
                #     "base": "http://example.org/txn/", 
                #     #"shape": "ex:AssetShape"  
                # }
                # "spend": {
                #     "rdf_property": "ex:spend",
                #     "base": "http://example.org/txn/", 
                #     "shape": "ex:AssetShape"  
                # }
            }
         },
        "ACCEPT_RETURN": {
            "properties": {
                **BASE_PROPERTIES,
                "sell_ref": {
                    "rdf_property": "ex:adv_ref",
                    "base": "http://example.org/txn/",  
                    #"shape": "ex:SellShape"  
                },
                # "request_return_ref": {
                #     "rdf_property": "ex:request_return_ref",
                #     "base": "http://example.org/txn/",  
                #     "shape": "ex:Request_ReturnShape"  
                # },
                # "spend": {
                # "rdf_property": "ex:spend",
                # "base": "http://example.org/txn/", 
                # #"shape": "ex:AssetShape"  
                #  }
            }
        }
}

# RDF Conversion Cache
class RDFConverter:
    def __init__(self):
        self.rdf_cache = {}
        #self.transaction_config = transaction_config

    @lru_cache(maxsize=None)  # Cache the static context part to avoid recalculating
    def get_static_context(self):
        """Return the static context part of the RDF data."""
        return STATIC_CONTEXT

    def process_property(self, prop, details, json_data, jsonld_data):
        """Process each property and add it to the JSON-LD data."""
        if prop in json_data:
            value = json_data[prop]
            if "base" in details:
                jsonld_data[details["rdf_property"]] = {
                    "@id": details["base"] + value
                }
            else:
                jsonld_data[details["rdf_property"]] = value

    def convert_json_to_rdf(self, json_data, transaction_config):
        """Convert JSON data to RDF graph with caching."""
        #start_time = time.time()

        # Check if the result is already cached based on the JSON data
        cache_key = json.dumps(json_data, sort_keys=True)
        if cache_key in self.rdf_cache:
            #logging.info("Cache hit: Returning cached RDF graph.")
            return self.rdf_cache[cache_key]
        if json_data["operation"] ==  "ADV":
            
            context = {
                "@context": {
                    "ex": "http://example.org/",
                    "schema": "http://schema.org/",
                    "transaction_id": "ex:transaction_id",
                    "operation": "ex:operation",
                    "status": "ex:status",
                    "ref": {
                        "@id": "ex:ref",
                        "@type": "@id"  # Ensure this is treated as a URI
                    }
                }
            }

            jsonld_data = {
                "@context": context["@context"],  # Reuse the existing context variable
                "@id": "http://example.org/txn/" + json_data["transaction_id"],
                "@type": "ex:" + json_data["operation"],
                "ref": "http://example.org/txn/" + json_data["asset_id"],  # Now ref is a URI
                "status": "Open"  # Literal value without prefix
            }
        else:
            # Context definition
            context = {
                "@context": {
                    "ex": "http://example.org/",
                    "schema": "http://schema.org/"
                }
            }

            # Assume json_data contains the incoming transaction data
            transaction_type = json_data.get("operation")
            config = transaction_config.get(transaction_type)

            if not config:
                raise ValueError(f"Unsupported transaction type: {transaction_type}")

            # Generate the JSON-LD structure dynamically based on the configuration
            jsonld_data = {
                "@context": context["@context"],
                "@id": "http://example.org/txn/" + json_data["transaction_id"],
                "@type": "ex:" + transaction_type
            }

            # for prop, details in config["properties"].items():
            #     self.process_property(prop, details, json_data, jsonld_data)

            # Dynamically assign properties based on the config
            for prop, details in config["properties"].items():
                if prop in json_data:
                    value = json_data[prop]
                    
                    # Check if the property has a base URL for URI creation
                    if "base" in details:
                        # Handle URI-based values like adv_ref and asset_ref
                        jsonld_data[details["rdf_property"]] = {
                            "@id": details["base"] + value  # Create the URI based on the base for both adv_ref and asset_ref
                        }
                    else:
                        # Handle literal values like transaction_id and operation
                        jsonld_data[details["rdf_property"]] = value          
            
        # Create RDF graph from the JSON-LD data
        g = Graph()
        g.parse(data=json.dumps(jsonld_data), format='json-ld')

        # Cache the RDF graph for future use
        self.rdf_cache[cache_key] = g

        # end_time = time.time()
        # logging.info(f"Time taken to convert JSON to RDF: {end_time - start_time} seconds")
        return g


# SHACL Validator


class SHACLValidator:
    def __init__(self, rdf_converter):
        #start_time = time.time()
    
        self.rdf_converter = rdf_converter  # Initialize RDFConverter
        self.shacl_graph = None
        self.existing_graph = Graph()
        script_dir = os.path.dirname(__file__)  # Get the script's directory
        self.ttl_file_path = os.path.join(script_dir, 'output.ttl')  # Path to the TTL file
        self.existing_graph_loaded = False  # Initialize the flag to track if the existing graph is loaded
        self._initialize_existing_graph()  # Initialize the existing graph when the class is instantiated
        self.validated_transactions = set()
        self.create_shape_cache = set() 
        # end_time = time.time()
        # logging.info(f"Time taken to __init__: {end_time - start_time} seconds")

    def _initialize_existing_graph(self):
        """Helper function to load or create the TTL file."""
        #start_time = time.time()
    
        if os.path.exists(self.ttl_file_path):
            try:
                self.existing_graph.parse(self.ttl_file_path, format='turtle')
                self.existing_graph_loaded = True  # Set the flag to True when the graph is loaded
                #logging.info("Existing TTL graph loaded successfully.")
            except Exception as e:
                logging.error(f"Error loading existing TTL file at {self.ttl_file_path}: {e}")
                # end_time = time.time()
                # logging.info(f"Time _initialize_existing_graph Iff: {end_time - start_time} seconds")
        else:
            # Create the file if it doesn't exist
            try:
                with open(self.ttl_file_path, 'w', encoding='utf-8') as f:
                    pass  # Create an empty file to initialize it
                self.existing_graph_loaded = True  # Set the flag to True after creating the file
                #logging.info(f"Created new empty TTL file at {self.ttl_file_path}")
            except Exception as e:
                logging.error(f"Error creating the TTL file at {self.ttl_file_path}: {e}")
                # end_time = time.time()
                # logging.info(f"_initialize_existing_graph Else: {end_time - start_time} seconds")    

    def load_shacl_graph(self, shacl_file_path):
        """Load SHACL graph once."""
        #start_time = time.time()
    
        if self.shacl_graph is None:
            try:
                
                self.shacl_graph = Graph()
                self.shacl_graph.parse(shacl_file_path, format='turtle')
                
            except Exception as e:
                logging.error(f"Error loading SHACL file at {shacl_file_path}: {e}")
        # end_time = time.time()
        # logging.info(f"Time taken to validate shape: {end_time - start_time} seconds")
    def update_existing_graph(self, new_graph):
        #start_time = time.time()
    
        """Update the existing graph with new graph data and append to file."""
        try:
            self.existing_graph += new_graph
            ttl_data = new_graph.serialize(format='turtle').decode('utf-8')
            with open(self.ttl_file_path, 'a', encoding='utf-8') as turtle_file:
                turtle_file.write(ttl_data)  # Append the new RDF data
            # logging.info(f"Successfully appended validated graph to {self.ttl_file_path}")
            # end_time = time.time()
            # logging.info(f"Time taken to update_existing_graph: {end_time - start_time} seconds")
        except Exception as e:
            logging.error(f"Error updating TTL file at {self.ttl_file_path}: {e}")

    def validate_shape(self, json_data):
        

        """Validate the shape of the incoming JSON data."""
        try:
            transaction_id = json_data["transaction_id"]
            if not self.shacl_graph or not self.existing_graph_loaded:
                raise Exception("SHACL or existing graph not loaded properly. Call initialize_graphs first.")

            # Convert the incoming JSON data to RDF format using caching
            rdf_graph = self.rdf_converter.convert_json_to_rdf(json_data, transaction_config)

            # Validate the new RDF graph against the existing graph (without combining them)
            #start_time = time.time()
            conforms, results_graph, results_text = validate(
                data_graph=rdf_graph,
                shacl_graph=self.shacl_graph,
                inference=None,
                debug=True
            )
            # end_time = time.time()
            # logging.info(f"Time taken to validate and update the graph: {end_time - start_time} seconds")
            if conforms:
                #logging.info("Validation successful")
                
               
                self.update_existing_graph(rdf_graph)  # Assuming this is needed for persistence
                self.validated_transactions.add(transaction_id) #not optimized
                
                return True
            else:
                # logging.error("Validation failed")
                # end_time = time.time()
                # logging.info(f"Time taken to validate shape ERROR: {end_time - start_time} seconds")
                return False
        except Exception as e:
            #logging.error(f"Error during shape validation: {e}")
            return False


def initialize_graphs(shacl_file_path, shacl_validator):
    """Initialize SHACL and existing graphs."""
    #start_time = time.time()

    # Only initialize if not already done
    if shacl_validator.shacl_graph is None:
        shacl_validator.load_shacl_graph(shacl_file_path)
    if not shacl_validator.existing_graph_loaded:
        shacl_validator._initialize_existing_graph()  # Using the private method to load or create the graph

    # end_time = time.time()
    # logging.info(f"Time taken to initialize graphs: {end_time - start_time} seconds")


# Initialize RDFConverter and SHACLValidator
rdf_converter = RDFConverter()  # Ensure you have the RDFConverter class or import it
shacl_validator = SHACLValidator(rdf_converter)
shacl_file_path = os.path.join(os.path.dirname(__file__), 'shacl_shape.ttl')

# Initialize SHACL and existing graphs once at the start
initialize_graphs(shacl_file_path, shacl_validator)

class Input(object):
    """A Input is used to spend assets locked by an Output.

    Wraps around a Crypto-condition Fulfillment.

        Attributes:
            fulfillment (:class:`cryptoconditions.Fulfillment`): A Fulfillment
                to be signed with a private key.
            owners_before (:obj:`list` of :obj:`str`): A list of owners after a
                Transaction was confirmed.
            fulfills (:class:`~bigchaindb.common.transaction. TransactionLink`,
                optional): A link representing the input of a `TRANSFER`
                Transaction.
    """

    def __init__(self, fulfillment, owners_before, fulfills=None):
        """Create an instance of an :class:`~.Input`.

        Args:
            fulfillment (:class:`cryptoconditions.Fulfillment`): A
                Fulfillment to be signed with a private key.
            owners_before (:obj:`list` of :obj:`str`): A list of owners
                after a Transaction was confirmed.
            fulfills (:class:`~bigchaindb.common.transaction.
                TransactionLink`, optional): A link representing the input
                of a `TRANSFER` Transaction.
        """
        if fulfills is not None and not isinstance(fulfills, TransactionLink):
            raise TypeError("`fulfills` must be a TransactionLink instance")
        if not isinstance(owners_before, list):
            raise TypeError("`owners_before` must be a list instance")

        self.fulfillment = fulfillment
        self.fulfills = fulfills
        self.owners_before = owners_before

    def __eq__(self, other):
        # TODO: If `other !== Fulfillment` return `False`
        return self.to_dict() == other.to_dict()

    # NOTE: This function is used to provide a unique key for a given
    # Input to suppliment memoization
    def __hash__(self):
        return hash((self.fulfillment, self.fulfills))

    def to_dict(self):
        """Transforms the object to a Python dictionary.

        Note:
            If an Input hasn't been signed yet, this method returns a
            dictionary representation.

        Returns:
            dict: The Input as an alternative serialization format.
        """
        try:
            fulfillment = self.fulfillment.serialize_uri()
        except (TypeError, AttributeError, ASN1EncodeError, ASN1DecodeError):
            fulfillment = _fulfillment_to_details(self.fulfillment)

        try:
            # NOTE: `self.fulfills` can be `None` and that's fine
            fulfills = self.fulfills.to_dict()
        except AttributeError:
            fulfills = None

        input_ = {
            "owners_before": self.owners_before,
            "fulfills": fulfills,
            "fulfillment": fulfillment,
        }
        return input_

    @classmethod
    def generate(cls, public_keys):
        # TODO: write docstring
        # The amount here does not really matter. It is only use on the
        # output data model but here we only care about the fulfillment
        output = Output.generate(public_keys, 1)
        return cls(output.fulfillment, public_keys)

    @classmethod
    def from_dict(cls, data):
        """Transforms a Python dictionary to an Input object.

        Note:
            Optionally, this method can also serialize a Cryptoconditions-
            Fulfillment that is not yet signed.

        Args:
            data (dict): The Input to be transformed.

        Returns:
            :class:`~bigchaindb.common.transaction.Input`

        Raises:
            InvalidSignature: If an Input's URI couldn't be parsed.
        """
        fulfillment = data["fulfillment"]
        if not isinstance(fulfillment, (Fulfillment, type(None))):
            try:
                fulfillment = Fulfillment.from_uri(data["fulfillment"])
            except ASN1DecodeError:
                # TODO Remove as it is legacy code, and simply fall back on
                # ASN1DecodeError
                raise InvalidSignature("Fulfillment URI couldn't been parsed")
            except TypeError:
                # NOTE: See comment about this special case in
                #       `Input.to_dict`
                fulfillment = _fulfillment_from_details(data["fulfillment"])
        fulfills = TransactionLink.from_dict(data["fulfills"])
        return cls(fulfillment, data["owners_before"], fulfills)


def _fulfillment_to_details(fulfillment):
    """Encode a fulfillment as a details dictionary

    Args:
        fulfillment: Crypto-conditions Fulfillment object
    """

    if fulfillment.type_name == "ed25519-sha-256":
        return {
            "type": "ed25519-sha-256",
            "public_key": base58.b58encode(fulfillment.public_key).decode(),
        }

    if fulfillment.type_name == "threshold-sha-256":
        subconditions = [
            _fulfillment_to_details(cond["body"]) for cond in fulfillment.subconditions
        ]
        return {
            "type": "threshold-sha-256",
            "threshold": fulfillment.threshold,
            "subconditions": subconditions,
        }

    raise UnsupportedTypeError(fulfillment.type_name)


def _fulfillment_from_details(data, _depth=0):
    """Load a fulfillment for a signing spec dictionary

    Args:
        data: tx.output[].condition.details dictionary
    """
    if _depth == 100:
        raise ThresholdTooDeep()

    if data["type"] == "ed25519-sha-256":
        public_key = base58.b58decode(data["public_key"])
        return Ed25519Sha256(public_key=public_key)

    if data["type"] == "threshold-sha-256":
        threshold = ThresholdSha256(data["threshold"])
        for cond in data["subconditions"]:
            cond = _fulfillment_from_details(cond, _depth + 1)
            threshold.add_subfulfillment(cond)
        return threshold

    raise UnsupportedTypeError(data.get("type"))


class TransactionLink(object):
    """An object for unidirectional linking to a Transaction's Output.

    Attributes:
        txid (str, optional): A Transaction to link to.
        output (int, optional): An output's index in a Transaction with id
        `txid`.
    """

    def __init__(self, txid=None, output=None):
        """Create an instance of a :class:`~.TransactionLink`.

        Note:
            In an IPLD implementation, this class is not necessary anymore,
            as an IPLD link can simply point to an object, as well as an
            objects properties. So instead of having a (de)serializable
            class, we can have a simple IPLD link of the form:
            `/<tx_id>/transaction/outputs/<output>/`.

        Args:
            txid (str, optional): A Transaction to link to.
            output (int, optional): An Outputs's index in a Transaction with
                id `txid`.
        """
        self.txid = txid
        self.output = output

    def __bool__(self):
        return self.txid is not None and self.output is not None

    def __eq__(self, other):
        # TODO: If `other !== TransactionLink` return `False`
        return self.to_dict() == other.to_dict()

    def __hash__(self):
        return hash((self.txid, self.output))

    @classmethod
    def from_dict(cls, link):
        """Transforms a Python dictionary to a TransactionLink object.

        Args:
            link (dict): The link to be transformed.

        Returns:
            :class:`~bigchaindb.common.transaction.TransactionLink`
        """
        try:
            return cls(link["transaction_id"], link["output_index"])
        except TypeError:
            return cls()

    def to_dict(self):
        """Transforms the object to a Python dictionary.

        Returns:
            (dict|None): The link as an alternative serialization format.
        """
        if self.txid is None and self.output is None:
            return None
        else:
            return {
                "transaction_id": self.txid,
                "output_index": self.output,
            }

    def to_uri(self, path=""):
        if self.txid is None and self.output is None:
            return None
        return "{}/transactions/{}/outputs/{}".format(path, self.txid, self.output)


class Output(object):
    """An Output is used to lock an asset.

    Wraps around a Crypto-condition Condition.

        Attributes:
            fulfillment (:class:`cryptoconditions.Fulfillment`): A Fulfillment
                to extract a Condition from.
            public_keys (:obj:`list` of :obj:`str`, optional): A list of
                owners before a Transaction was confirmed.
    """

    MAX_AMOUNT = 9 * 10 ** 18

    def __init__(self, fulfillment, public_keys=None, amount=1):
        """Create an instance of a :class:`~.Output`.

        Args:
            fulfillment (:class:`cryptoconditions.Fulfillment`): A
                Fulfillment to extract a Condition from.
            public_keys (:obj:`list` of :obj:`str`, optional): A list of
                owners before a Transaction was confirmed.
            amount (int): The amount of Assets to be locked with this
                Output.

        Raises:
            TypeError: if `public_keys` is not instance of `list`.
        """
        if not isinstance(public_keys, list) and public_keys is not None:
            raise TypeError("`public_keys` must be a list instance or None")
        if not isinstance(amount, int):
            raise TypeError("`amount` must be an int")
        if amount < 1:
            raise AmountError("`amount` must be greater than 0")
        if amount > self.MAX_AMOUNT:
            raise AmountError("`amount` must be <= %s" % self.MAX_AMOUNT)

        self.fulfillment = fulfillment
        self.amount = amount
        self.public_keys = public_keys

    def __eq__(self, other):
        # TODO: If `other !== Condition` return `False`
        return self.to_dict() == other.to_dict()

    def to_dict(self):
        """Transforms the object to a Python dictionary.

        Note:
            A dictionary serialization of the Input the Output was
            derived from is always provided.

        Returns:
            dict: The Output as an alternative serialization format.
        """
        # TODO FOR CC: It must be able to recognize a hashlock condition
        #              and fulfillment!
        condition = {}
        try:
            condition["details"] = _fulfillment_to_details(self.fulfillment)
        except AttributeError:
            pass

        try:
            condition["uri"] = self.fulfillment.condition_uri
        except AttributeError:
            condition["uri"] = self.fulfillment

        output = {
            "public_keys": self.public_keys,
            "condition": condition,
            "amount": str(self.amount),
        }
        return output

    @classmethod
    def generate(cls, public_keys, amount):
        """Generates a Output from a specifically formed tuple or list.

        Note:
            If a ThresholdCondition has to be generated where the threshold
            is always the number of subconditions it is split between, a
            list of the following structure is sufficient:

            [(address|condition)*, [(address|condition)*, ...], ...]

        Args:
            public_keys (:obj:`list` of :obj:`str`): The public key of
                the users that should be able to fulfill the Condition
                that is being created.
            amount (:obj:`int`): The amount locked by the Output.

        Returns:
            An Output that can be used in a Transaction.

        Raises:
            TypeError: If `public_keys` is not an instance of `list`.
            ValueError: If `public_keys` is an empty list.
        """
        threshold = len(public_keys)
        if not isinstance(amount, int):
            raise TypeError("`amount` must be a int")
        if amount < 1:
            raise AmountError("`amount` needs to be greater than zero")
        if not isinstance(public_keys, list):
            raise TypeError("`public_keys` must be an instance of list")
        if len(public_keys) == 0:
            raise ValueError("`public_keys` needs to contain at least one" "owner")
        elif len(public_keys) == 1 and not isinstance(public_keys[0], list):
            if isinstance(public_keys[0], Fulfillment):
                ffill = public_keys[0]
            else:
                ffill = Ed25519Sha256(public_key=base58.b58decode(public_keys[0]))
            return cls(ffill, public_keys, amount=amount)
        else:
            initial_cond = ThresholdSha256(threshold=threshold)
            threshold_cond = reduce(cls._gen_condition, public_keys, initial_cond)
            return cls(threshold_cond, public_keys, amount=amount)

    @classmethod
    def _gen_condition(cls, initial, new_public_keys):
        """Generates ThresholdSha256 conditions from a list of new owners.

        Note:
            This method is intended only to be used with a reduce function.
            For a description on how to use this method, see
            :meth:`~.Output.generate`.

        Args:
            initial (:class:`cryptoconditions.ThresholdSha256`):
                A Condition representing the overall root.
            new_public_keys (:obj:`list` of :obj:`str`|str): A list of new
                owners or a single new owner.

        Returns:
            :class:`cryptoconditions.ThresholdSha256`:
        """
        try:
            threshold = len(new_public_keys)
        except TypeError:
            threshold = None

        if isinstance(new_public_keys, list) and len(new_public_keys) > 1:
            ffill = ThresholdSha256(threshold=threshold)
            reduce(cls._gen_condition, new_public_keys, ffill)
        elif isinstance(new_public_keys, list) and len(new_public_keys) <= 1:
            raise ValueError("Sublist cannot contain single owner")
        else:
            try:
                new_public_keys = new_public_keys.pop()
            except AttributeError:
                pass
            # NOTE: Instead of submitting base58 encoded addresses, a user
            #       of this class can also submit fully instantiated
            #       Cryptoconditions. In the case of casting
            #       `new_public_keys` to a Ed25519Fulfillment with the
            #       result of a `TypeError`, we're assuming that
            #       `new_public_keys` is a Cryptocondition then.
            if isinstance(new_public_keys, Fulfillment):
                ffill = new_public_keys
            else:
                ffill = Ed25519Sha256(public_key=base58.b58decode(new_public_keys))
        initial.add_subfulfillment(ffill)
        return initial

    @classmethod
    def from_dict(cls, data):
        """Transforms a Python dictionary to an Output object.

        Note:
            To pass a serialization cycle multiple times, a
            Cryptoconditions Fulfillment needs to be present in the
            passed-in dictionary, as Condition URIs are not serializable
            anymore.

        Args:
            data (dict): The dict to be transformed.

        Returns:
            :class:`~bigchaindb.common.transaction.Output`
        """
        try:
            fulfillment = _fulfillment_from_details(data["condition"]["details"])
        except KeyError:
            # NOTE: Hashlock condition case
            fulfillment = data["condition"]["uri"]
        try:
            amount = int(data["amount"])
        except ValueError:
            raise AmountError("Invalid amount: %s" % data["amount"])
        return cls(fulfillment, data["public_keys"], amount)


class Transaction(object):
    """A Transaction is used to create and transfer assets.

    Note:
        For adding Inputs and Outputs, this class provides methods
        to do so.

    Attributes:
        operation (str): Defines the operation of the Transaction.
        inputs (:obj:`list` of :class:`~bigchaindb.common.
            transaction.Input`, optional): Define the assets to
            spend.
        outputs (:obj:`list` of :class:`~bigchaindb.common.
            transaction.Output`, optional): Define the assets to lock.
        asset (dict): Asset payload for this Transaction. ``CREATE``
            Transactions require a dict with a ``data``
            property while ``TRANSFER`` Transactions require a dict with a
            ``id`` property.
        metadata (dict):
            Metadata to be stored along with the Transaction.
        version (string): Defines the version number of a Transaction.
    """

    CREATE = "CREATE"
    TRANSFER = "TRANSFER"
    PRE_REQUEST = "PRE_REQUEST"
    INTEREST = "INTEREST"
    REQUEST_FOR_QUOTE = "REQUEST_FOR_QUOTE"
    BID = "BID"
    ACCEPT = "ACCEPT"
    RETURN = "RETURN"
    BUYOFFER = "BUYOFFER"
    ADV = "ADV" 
    SELL = "SELL"
    INVERSE_TXN = "INVERSE_TXN"
    ACCEPT_RETURN = "ACCEPT_RETURN"
    UPDATE_ADV = "UPDATE_ADV" 
    ALLOWED_OPERATIONS = (
        CREATE,
        TRANSFER,
        PRE_REQUEST,
        INTEREST,
        REQUEST_FOR_QUOTE,
        BID,
        ACCEPT,
        RETURN,
        BUYOFFER,
        ADV, 
        SELL,
        INVERSE_TXN,
        ACCEPT_RETURN,
        UPDATE_ADV,
    )
    VERSION = "2.0"

    def __init__(
        self,
        operation,
        asset,
        inputs=None,
        outputs=None,
        metadata=None,
        version=None,
        hash_id=None,
        tx_dict=None,
    ):
        """The constructor allows to create a customizable Transaction.

        Note:
            When no `version` is provided, one is being
            generated by this method.

        Args:
            operation (str): Defines the operation of the Transaction.
            asset (dict): Asset payload for this Transaction.
            inputs (:obj:`list` of :class:`~bigchaindb.common.
                transaction.Input`, optional): Define the assets to
            outputs (:obj:`list` of :class:`~bigchaindb.common.
                transaction.Output`, optional): Define the assets to
                lock.
            metadata (dict): Metadata to be stored along with the
                Transaction.
            version (string): Defines the version number of a Transaction.
            hash_id (string): Hash id of the transaction.
        """
        if operation not in self.ALLOWED_OPERATIONS:
            allowed_ops = ", ".join(self.__class__.ALLOWED_OPERATIONS)
            raise ValueError("`operation` must be one of {}".format(allowed_ops))

        # Asset payloads for 'CREATE' operations must be None or
        # dicts holding a `data` property. Asset payloads for 'TRANSFER'
        # operations must be dicts holding an `id` property.
        if (
            (operation == self.CREATE or operation == self.BID or operation == self.BUYOFFER or operation == self.SELL or operation == self.PRE_REQUEST or operation == self.INTEREST)
            and asset is not None
            and not (isinstance(asset, dict) and "data" in asset)
        ):
            raise TypeError(
                (
                    "`asset` must be None or a dict holding a `data` "
                    " property instance for '{}' Transactions".format(operation)
                )
            )
        elif operation == self.TRANSFER and not (
            isinstance(asset, dict) and "id" in asset
        ):
            raise TypeError(
                (
                    "`asset` must be a dict holding an `id` property "
                    "for 'TRANSFER' Transactions".format(operation)
                )
            )
        elif (
            (
                # operation == self.PRE_REQUEST
                # or 
                operation == self.REQUEST_FOR_QUOTE
                or operation == self.ACCEPT
                or operation == self.ADV
                or operation == self.UPDATE_ADV
                
            )
            and asset is not None
            and not (isinstance(asset, dict))
        ):
            raise TypeError(
                (
                    "`asset` must be a dict"
                    "for 'REQUEST_FOR_QUOTE' Transactions".format(operation)
                )
            )
        elif (operation == self.INTEREST or operation == self.BID  or operation == self.BUYOFFER or operation == self.SELL or operation == self.PRE_REQUEST ) and not (
            isinstance(asset, dict)
        ):
            raise TypeError(
                (
                    "`asset` must be a dict holding an `id` property  "
                    "for 'INTEREST' Transactions".format(operation)
                )
            )

        if outputs and not isinstance(outputs, list):
            raise TypeError("`outputs` must be a list instance or None")

        if inputs and not isinstance(inputs, list):
            raise TypeError("`inputs` must be a list instance or None")

        if metadata is not None and not isinstance(metadata, dict):
            raise TypeError("`metadata` must be a dict or None")

        self.version = version if version is not None else self.VERSION
        self.operation = operation
        self.asset = asset
        self.inputs = inputs or []
        self.outputs = outputs or []
        self.metadata = metadata
        self._id = hash_id
        self.tx_dict = tx_dict
        self.open_advertisements = {}
    @property
    def unspent_outputs(self):
        """UnspentOutput: The outputs of this transaction, in a data
        structure containing relevant information for storing them in
        a UTXO set, and performing validation.
        """
        if self.operation == self.CREATE:
            self._asset_id = self._id
        elif self.operation == self.TRANSFER:
            self._asset_id = self.asset["id"]
        # elif self.operation == self.INTEREST:
        #     self._asset_id = self.asset["id"]
        # FIXME: Add PRE_REQUEST, INTEREST, and BID-ACCEPT
        return (
            UnspentOutput(
                transaction_id=self._id,
                output_index=output_index,
                amount=output.amount,
                asset_id=self._asset_id,
                condition_uri=output.fulfillment.condition_uri,
            )
            for output_index, output in enumerate(self.outputs)
        )

    @property
    def spent_outputs(self):
        """Tuple of :obj:`dict`: Inputs of this transaction. Each input
        is represented as a dictionary containing a transaction id and
        output index.
        """
        return (input_.fulfills.to_dict() for input_ in self.inputs if input_.fulfills)

    @property
    def serialized(self):
        return Transaction._to_str(self.to_dict())

    def _hash(self):
        self._id = hash_data(self.serialized)

    @classmethod
    def validate_create(cls, tx_signers, recipients, asset, metadata):
        if not isinstance(tx_signers, list):
            raise TypeError("`tx_signers` must be a list instance")
        if not isinstance(recipients, list):
            raise TypeError("`recipients` must be a list instance")
        if len(tx_signers) == 0:
            raise ValueError("`tx_signers` list cannot be empty")
        if len(recipients) == 0:
            raise ValueError("`recipients` list cannot be empty")
        if not (asset is None or isinstance(asset, dict)):
            raise TypeError("`asset` must be a dict or None")
        if not (metadata is None or isinstance(metadata, dict)):
            raise TypeError("`metadata` must be a dict or None")

        inputs = []
        outputs = []

        # generate_outputs
        for recipient in recipients:
            if not isinstance(recipient, tuple) or len(recipient) != 2:
                raise ValueError(
                    (
                        "Each `recipient` in the list must be a"
                        " tuple of `([<list of public keys>],"
                        " <amount>)`"
                    )
                )
            pub_keys, amount = recipient
            outputs.append(Output.generate(pub_keys, amount))

        # generate inputs
        inputs.append(Input.generate(tx_signers))

        return (inputs, outputs)

    @classmethod
    def create(cls, tx_signers, recipients, metadata=None, asset=None):
        """A simple way to generate a `CREATE` transaction.

        Note:
            This method currently supports the following Cryptoconditions
            use cases:
                - Ed25519
                - ThresholdSha256

            Additionally, it provides support for the following BigchainDB
            use cases:
                - Multiple inputs and outputs.

        Args:
            tx_signers (:obj:`list` of :obj:`str`): A list of keys that
                represent the signers of the CREATE Transaction.
            recipients (:obj:`list` of :obj:`tuple`): A list of
                ([keys],amount) that represent the recipients of this
                Transaction.
            metadata (dict): The metadata to be stored along with the
                Transaction.
            asset (dict): The metadata associated with the asset that will
                be created in this Transaction.

        Returns:
            :class:`~bigchaindb.common.transaction.Transaction`
        """

        (inputs, outputs) = cls.validate_create(tx_signers, recipients, asset, metadata)
        return cls(cls.CREATE, {"data1": asset}, inputs, outputs, metadata)

    @classmethod
    def validate_transfer(cls, inputs, recipients, asset_id, metadata):
        if not isinstance(inputs, list):
            raise TypeError("`inputs` must be a list instance")
        if len(inputs) == 0:
            raise ValueError("`inputs` must contain at least one item")
        if not isinstance(recipients, list):
            raise TypeError("`recipients` must be a list instance")
        if len(recipients) == 0:
            raise ValueError("`recipients` list cannot be empty")

        outputs = []
        for recipient in recipients:
            if not isinstance(recipient, tuple) or len(recipient) != 2:
                raise ValueError(
                    (
                        "Each `recipient` in the list must be a"
                        " tuple of `([<list of public keys>],"
                        " <amount>)`"
                    )
                )
            pub_keys, amount = recipient
            outputs.append(Output.generate(pub_keys, amount))

        if not isinstance(asset_id, str):
            raise TypeError("`asset_id` must be a string")

        
        return (deepcopy(inputs), outputs)

    @classmethod
    def transfer(cls, inputs, recipients, asset_id, metadata=None):
        """A simple way to generate a `TRANSFER` transaction.

        Note:
            Different cases for threshold conditions:

            Combining multiple `inputs` with an arbitrary number of
            `recipients` can yield interesting cases for the creation of
            threshold conditions we'd like to support. The following
            notation is proposed:

            1. The index of a `recipient` corresponds to the index of
               an input:
               e.g. `transfer([input1], [a])`, means `input1` would now be
                    owned by user `a`.

            2. `recipients` can (almost) get arbitrary deeply nested,
               creating various complex threshold conditions:
               e.g. `transfer([inp1, inp2], [[a, [b, c]], d])`, means
                    `a`'s signature would have a 50% weight on `inp1`
                    compared to `b` and `c` that share 25% of the leftover
                    weight respectively. `inp2` is owned completely by `d`.

        Args:
            inputs (:obj:`list` of :class:`~bigchaindb.common.transaction.
                Input`): Converted `Output`s, intended to
                be used as inputs in the transfer to generate.
            recipients (:obj:`list` of :obj:`tuple`): A list of
                ([keys],amount) that represent the recipients of this
                Transaction.
            asset_id (str): The asset ID of the asset to be transferred in
                this Transaction.
            metadata (dict): Python dictionary to be stored along with the
                Transaction.

        Returns:
            :class:`~bigchaindb.common.transaction.Transaction`
        """
        (inputs, outputs) = cls.validate_transfer(
            inputs, recipients, asset_id, metadata
        )
        return cls(cls.TRANSFER, {"id": asset_id}, inputs, outputs, metadata)

    def __eq__(self, other):
        try:
            other = other.to_dict()
        except AttributeError:
            return False
        return self.to_dict() == other

    def to_inputs(self, indices=None):
        """Converts a Transaction's outputs to spendable inputs.

        Note:
            Takes the Transaction's outputs and derives inputs
            from that can then be passed into `Transaction.transfer` as
            `inputs`.
            A list of integers can be passed to `indices` that
            defines which outputs should be returned as inputs.
            If no `indices` are passed (empty list or None) all
            outputs of the Transaction are returned.

        Args:
            indices (:obj:`list` of int): Defines which
                outputs should be returned as inputs.

        Returns:
            :obj:`list` of :class:`~bigchaindb.common.transaction.
                Input`
        """
        # NOTE: If no indices are passed, we just assume to take all outputs
        #       as inputs.
        indices = indices or range(len(self.outputs))
        return [
            Input(
                self.outputs[idx].fulfillment,
                self.outputs[idx].public_keys,
                TransactionLink(self.id, idx),
            )
            for idx in indices
        ]

    def add_input(self, input_):
        """Adds an input to a Transaction's list of inputs.

        Args:
            input_ (:class:`~bigchaindb.common.transaction.
                Input`): An Input to be added to the Transaction.
        """
        if not isinstance(input_, Input):
            raise TypeError("`input_` must be a Input instance")
        self.inputs.append(input_)

    def add_output(self, output):
        """Adds an output to a Transaction's list of outputs.

        Args:
            output (:class:`~bigchaindb.common.transaction.
                Output`): An Output to be added to the
                Transaction.
        """
        if not isinstance(output, Output):
            raise TypeError("`output` must be an Output instance or None")
        self.outputs.append(output)

    def sign(self, private_keys):
        """Fulfills a previous Transaction's Output by signing Inputs.

        Note:
            This method works only for the following Cryptoconditions
            currently:
                - Ed25519Fulfillment
                - ThresholdSha256
            Furthermore, note that all keys required to fully sign the
            Transaction have to be passed to this method. A subset of all
            will cause this method to fail.

        Args:
            private_keys (:obj:`list` of :obj:`str`): A complete list of
                all private keys needed to sign all Fulfillments of this
                Transaction.

        Returns:
            :class:`~bigchaindb.common.transaction.Transaction`
        """
        # TODO: Singing should be possible with at least one of all private
        #       keys supplied to this method.
        if private_keys is None or not isinstance(private_keys, list):
            raise TypeError("`private_keys` must be a list instance")

        # NOTE: Generate public keys from private keys and match them in a
        #       dictionary:
        #                   key:     public_key
        #                   value:   private_key
        def gen_public_key(private_key):
            # TODO FOR CC: Adjust interface so that this function becomes
            #              unnecessary

            # cc now provides a single method `encode` to return the key
            # in several different encodings.
            public_key = private_key.get_verifying_key().encode()
            # Returned values from cc are always bytestrings so here we need
            # to decode to convert the bytestring into a python str
            return public_key.decode()

        key_pairs = {
            gen_public_key(PrivateKey(private_key)): PrivateKey(private_key)
            for private_key in private_keys
        }

        tx_dict = self.to_dict()
        tx_dict = Transaction._remove_signatures(tx_dict)
        tx_serialized = Transaction._to_str(tx_dict)
        for i, input_ in enumerate(self.inputs):
            self.inputs[i] = self._sign_input(input_, tx_serialized, key_pairs)

        self._hash()

        return self

    @classmethod
    def _sign_input(cls, input_, message, key_pairs):
        """Signs a single Input.

        Note:
            This method works only for the following Cryptoconditions
            currently:
                - Ed25519Fulfillment
                - ThresholdSha256.

        Args:
            input_ (:class:`~bigchaindb.common.transaction.
                Input`) The Input to be signed.
            message (str): The message to be signed
            key_pairs (dict): The keys to sign the Transaction with.
        """
        if isinstance(input_.fulfillment, Ed25519Sha256):
            return cls._sign_simple_signature_fulfillment(input_, message, key_pairs)
        elif isinstance(input_.fulfillment, ThresholdSha256):
            return cls._sign_threshold_signature_fulfillment(input_, message, key_pairs)
        else:
            raise ValueError(
                "Fulfillment couldn't be matched to "
                "Cryptocondition fulfillment type."
            )

    @classmethod
    def _sign_simple_signature_fulfillment(cls, input_, message, key_pairs):
        """Signs a Ed25519Fulfillment.

        Args:
            input_ (:class:`~bigchaindb.common.transaction.
                Input`) The input to be signed.
            message (str): The message to be signed
            key_pairs (dict): The keys to sign the Transaction with.
        """
        # NOTE: To eliminate the dangers of accidentally signing a condition by
        #       reference, we remove the reference of input_ here
        #       intentionally. If the user of this class knows how to use it,
        #       this should never happen, but then again, never say never.
        input_ = deepcopy(input_)
        public_key = input_.owners_before[0]
        message = sha3_256(message.encode())
        if input_.fulfills:
            message.update(
                "{}{}".format(input_.fulfills.txid, input_.fulfills.output).encode()
            )

        try:
            # cryptoconditions makes no assumptions of the encoding of the
            # message to sign or verify. It only accepts bytestrings
            input_.fulfillment.sign(
                message.digest(), base58.b58decode(key_pairs[public_key].encode())
            )
        except KeyError:
            raise KeypairMismatchException(
                "Public key {} is not a pair to "
                "any of the private keys".format(public_key)
            )
        return input_

    @classmethod
    def _sign_threshold_signature_fulfillment(cls, input_, message, key_pairs):
        """Signs a ThresholdSha256.

        Args:
            input_ (:class:`~bigchaindb.common.transaction.
                Input`) The Input to be signed.
            message (str): The message to be signed
            key_pairs (dict): The keys to sign the Transaction with.
        """
        input_ = deepcopy(input_)
        message = sha3_256(message.encode())
        if input_.fulfills:
            message.update(
                "{}{}".format(input_.fulfills.txid, input_.fulfills.output).encode()
            )

        for owner_before in set(input_.owners_before):
            # TODO: CC should throw a KeypairMismatchException, instead of
            #       our manual mapping here

            # TODO FOR CC: Naming wise this is not so smart,
            #              `get_subcondition` in fact doesn't return a
            #              condition but a fulfillment

            # TODO FOR CC: `get_subcondition` is singular. One would not
            #              expect to get a list back.
            ccffill = input_.fulfillment
            subffills = ccffill.get_subcondition_from_vk(base58.b58decode(owner_before))
            if not subffills:
                raise KeypairMismatchException(
                    "Public key {} cannot be found "
                    "in the fulfillment".format(owner_before)
                )
            try:
                private_key = key_pairs[owner_before]
            except KeyError:
                raise KeypairMismatchException(
                    "Public key {} is not a pair "
                    "to any of the private keys".format(owner_before)
                )

            # cryptoconditions makes no assumptions of the encoding of the
            # message to sign or verify. It only accepts bytestrings
            for subffill in subffills:
                subffill.sign(message.digest(), base58.b58decode(private_key.encode()))
        return input_

    def inputs_valid(self, outputs=None, bigchain=None):
        """Validates the Inputs in the Transaction against given
        Outputs.

            Note:
                Given a `CREATE` Transaction is passed,
                dummy values for Outputs are submitted for validation that
                evaluate parts of the validation-checks to `True`.

            Args:
                outputs (:obj:`list` of :class:`~bigchaindb.common.
                    transaction.Output`): A list of Outputs to check the
                    Inputs against.

            Returns:
                bool: If all Inputs are valid.
        
        ccffill = self.inputs[0].fulfillment
        if "Signature is: " in ccffill:
            if (
                self.operation == self.REQUEST_FOR_QUOTE
                or self.operation == self.ACCEPT
            ):
                RID = self.metadata["RID"]
                nonce = self.metadata["previous_nonce"]
                previous_transaction_ID = self.metadata["previous_transaction_ID"]
                result = bigchain.get_transaction(previous_transaction_ID)

                hashResult = result["metadata"]["hash"]
                if not self.hashVerify(hashResult, RID, nonce):
                    return False

            return self.GVerify(
                self.inputs[0].owners_before[0], ccffill, "seralization"
            )
        else:"""
        if self.operation in [
            self.CREATE,
            #self.PRE_REQUEST,
            self.REQUEST_FOR_QUOTE,
            #self.INTEREST,
            self.ACCEPT,
            self.ADV,
            self.UPDATE_ADV,
            
        ]:
            # NOTE: Since in the case of a `CREATE`-transaction we do not have
            #       to check for outputs, we're just submitting dummy
            #       values to the actual method. This simplifies it's logic
            #       greatly, as we do not have to check against `None` values.
            #This part should comment if not shacl validation
            if(self.operation == self.CREATE):
                self.generateShape()
            #end comment area    
            return self._inputs_valid(["dummyvalue" for _ in self.inputs])
        elif self.operation in [self.TRANSFER, self.BID, self.RETURN, self.BUYOFFER, self.SELL, self.INTEREST, self.PRE_REQUEST]:
            return self._inputs_valid(
                [output.fulfillment.condition_uri for output in outputs]
            )
        else:
            allowed_ops = ", ".join(self.__class__.ALLOWED_OPERATIONS)
            raise TypeError("`operation` must be one of {}".format(allowed_ops))

    def _inputs_valid(self, output_condition_uris):
        """Validates an Input against a given set of Outputs.

        Note:
            The number of `output_condition_uris` must be equal to the
            number of Inputs a Transaction has.

        Args:
            output_condition_uris (:obj:`list` of :obj:`str`): A list of
                Outputs to check the Inputs against.

        Returns:
            bool: If all Outputs are valid.
        """

        if len(self.inputs) != len(output_condition_uris):
            raise ValueError(
                "Inputs and " "output_condition_uris must have the same count"
            )

        tx_dict = self.tx_dict if self.tx_dict else self.to_dict()
        tx_dict = Transaction._remove_signatures(tx_dict)
        tx_dict["id"] = None
        tx_serialized = Transaction._to_str(tx_dict)

        def validate(i, output_condition_uri=None):
            """Validate input against output condition URI"""
            return self._input_valid(
                self.inputs[i], self.operation, tx_serialized, output_condition_uri
            )

        return all(validate(i, cond) for i, cond in enumerate(output_condition_uris))

    @lru_cache(maxsize=16384)
    def _input_valid(self, input_, operation, message, output_condition_uri=None):
        """Validates a single Input against a single Output.

        Note:
            In case of a `CREATE` Transaction, this method
            does not validate against `output_condition_uri`.

        Args:
            input_ (:class:`~bigchaindb.common.transaction.
                Input`) The Input to be signed.
            operation (str): The type of Transaction.
            message (str): The fulfillment message.
            output_condition_uri (str, optional): An Output to check the
                Input against.

        Returns:
            bool: If the Input is valid.
        """
        ccffill = input_.fulfillment
        try:
            parsed_ffill = Fulfillment.from_uri(ccffill.serialize_uri())
        except (TypeError, ValueError, ParsingError, ASN1DecodeError, ASN1EncodeError):
            return False

        if operation in [
            self.CREATE,
            #self.PRE_REQUEST,
            self.REQUEST_FOR_QUOTE,
            #self.INTEREST,
            self.ACCEPT,
            self.ADV,
            self.UPDATE_ADV,
        ]:
            # NOTE: In the case of a `CREATE` transaction, the
            #       output is always valid.
            output_valid = True
        else:
            output_valid = output_condition_uri == ccffill.condition_uri

        message = sha3_256(message.encode())
        if input_.fulfills:
            message.update(
                "{}{}".format(input_.fulfills.txid, input_.fulfills.output).encode()
            )

        # NOTE: We pass a timestamp to `.validate`, as in case of a timeout
        #       condition we'll have to validate against it

        # cryptoconditions makes no assumptions of the encoding of the
        # message to sign or verify. It only accepts bytestrings
        ffill_valid = parsed_ffill.validate(message=message.digest())
        return output_valid and ffill_valid

    def GVerify(self, group_public_key, signature, seralization):
        newSign = signature.replace(",", "comma").replace('"', "'")
        newSign2 = newSign.replace("Signature is: ((", '"((').replace("') ", "') \"")
        seralization2 = '"' + seralization + '"'

        dangerousString = (
            ". $HOME/.cargo/env; cd bigchaindb/common/ursa_Master/libzmix; cargo test test_scenario_1 --release --no-default-features --features PS_Signature_G1 -- GVerify,"
            + group_public_key
            + ","
            + newSign2
            + ","
            + seralization2
            + " --nocapture;"
        )

        p = Popen(dangerousString, stderr=PIPE, stdout=PIPE, shell=True)
        output, err = p.communicate(b"input data that is passed to subprocess' stdin")
        return "verified_signature_13: true" in output.decode("utf-8")

    def java_string_hashcode(self, s):
        h = 0
        for c in s:
            h = (31 * h + ord(c)) & 0xFFFFFFFF
        return ((h + 0x80000000) & 0xFFFFFFFF) - 0x80000000

    def hashVerify(self, hashResult, RID, nonce):
        hashTest = self.java_string_hashcode(RID + nonce)
        return hashTest == hashResult

    # This function is required by `lru_cache` to create a key for memoization
    def __hash__(self):
        return hash(self.id)

    @memoize_to_dict
    def to_dict(self):
        """Transforms the object to a Python dictionary.

        Returns:
            dict: The Transaction as an alternative serialization format.
        """
        return {
            "inputs": [input_.to_dict() for input_ in self.inputs],
            "outputs": [output.to_dict() for output in self.outputs],
            "operation": str(self.operation),
            "metadata": self.metadata,
            "asset": self.asset,
            "version": self.version,
            "id": self._id,
        }

    @staticmethod
    # TODO: Remove `_dict` prefix of variable.
    def _remove_signatures(tx_dict):
        """Takes a Transaction dictionary and removes all signatures.

        Args:
            tx_dict (dict): The Transaction to remove all signatures from.

        Returns:
            dict

        """
        # NOTE: We remove the reference since we need `tx_dict` only for the
        #       transaction's hash
        tx_dict = deepcopy(tx_dict)
        for input_ in tx_dict["inputs"]:
            # NOTE: Not all Cryptoconditions return a `signature` key (e.g.
            #       ThresholdSha256), so setting it to `None` in any
            #       case could yield incorrect signatures. This is why we only
            #       set it to `None` if it's set in the dict.
            input_["fulfillment"] = None
        return tx_dict

    @staticmethod
    def _to_hash(value):
        return hash_data(value)

    @property
    def id(self):
        return self._id

    def to_hash(self):
        return self.to_dict()["id"]

    @staticmethod
    def _to_str(value):
        return serialize(value)

    # TODO: This method shouldn't call `_remove_signatures`
    def __str__(self):
        tx = Transaction._remove_signatures(self.to_dict())
        return Transaction._to_str(tx)

    @classmethod
    def get_asset_id(cls, transactions):
        """Get the asset id from a list of :class:`~.Transactions`.

        This is useful when we want to check if the multiple inputs of a
        transaction are related to the same asset id.

        Args:
            transactions (:obj:`list` of :class:`~bigchaindb.common.
                transaction.Transaction`): A list of Transactions.
                Usually input Transactions that should have a matching
                asset ID.

        Returns:
            str: ID of the asset.

        Raises:
            :exc:`AssetIdMismatch`: If the inputs are related to different
                assets.
        """

        if not isinstance(transactions, list):
            transactions = [transactions]

        # create a set of the transactions' asset ids
        asset_ids = set()
        for tx in transactions:
            if tx.operation in [tx.CREATE, tx.BID, tx.BUYOFFER, tx.SELL, tx.PRE_REQUEST, tx.INTEREST, tx.ACCEPT_RETURN]: 
                asset_id = tx.id
            else:
                asset_id = tx.asset["id"]
            asset_ids.add(asset_id)

        # check that all the transasctions have the same asset id
        if len(asset_ids) > 1:
            raise AssetIdMismatch(
                (
                    "All inputs of all transactions passed"
                    " need to have the same asset id"
                )
            )
        return asset_ids.pop()

    @staticmethod
    def validate_id(tx_body):
        """Validate the transaction ID of a transaction

        Args:
            tx_body (dict): The Transaction to be transformed.
        """
        # NOTE: Remove reference to avoid side effects
        # tx_body = deepcopy(tx_body)
        tx_body = rapidjson.loads(rapidjson.dumps(tx_body))

        try:
            proposed_tx_id = tx_body["id"]
        except KeyError:
            raise InvalidHash("No transaction id found!")

        tx_body["id"] = None

        tx_body_serialized = Transaction._to_str(tx_body)
        valid_tx_id = Transaction._to_hash(tx_body_serialized)

        if proposed_tx_id != valid_tx_id:
            err_msg = (
                "The transaction's id '{}' isn't equal to "
                "the hash of its body, i.e. it's not valid."
            )
            raise InvalidHash(err_msg.format(proposed_tx_id))

    @classmethod
    @memoize_from_dict
    def from_dict(cls, tx, skip_schema_validation=True):
        """Transforms a Python dictionary to a Transaction object.

        Args:
            tx_body (dict): The Transaction to be transformed.

        Returns:
            :class:`~bigchaindb.common.transaction.Transaction`
        """
        operation = (
            tx.get("operation", Transaction.CREATE)
            if isinstance(tx, dict)
            else Transaction.CREATE
        )
        cls = Transaction.resolve_class(operation)

        if not skip_schema_validation:
            cls.validate_id(tx)
            cls.validate_schema(tx)

        inputs = [Input.from_dict(input_) for input_ in tx["inputs"]]
        outputs = [Output.from_dict(output) for output in tx["outputs"]]
        return cls(
            tx["operation"],
            tx["asset"],
            inputs,
            outputs,
            tx["metadata"],
            tx["version"],
            hash_id=tx["id"],
            tx_dict=tx,
        )

    @classmethod
    def from_db(cls, bigchain, tx_dict_list):
        """Helper method that reconstructs a transaction dict that was returned
        from the database. It checks what asset_id to retrieve, retrieves the
        asset from the asset table and reconstructs the transaction.

        Args:
            bigchain (:class:`~bigchaindb.tendermint.BigchainDB`): An instance
                of BigchainDB used to perform database queries.
            tx_dict_list (:list:`dict` or :obj:`dict`): The transaction dict or
                list of transaction dict as returned from the database.

        Returns:
            :class:`~Transaction`

        """
        return_list = True
        if isinstance(tx_dict_list, dict):
            tx_dict_list = [tx_dict_list]
            return_list = False

        tx_map = {}
        tx_ids = []
        for tx in tx_dict_list:
            tx.update({"metadata": None})
            tx_map[tx["id"]] = tx
            tx_ids.append(tx["id"])

        assets = list(bigchain.get_assets(tx_ids))
        for asset in assets:
            if asset is not None:
                tx = tx_map[asset["id"]]
                del asset["id"]
                tx["asset"] = asset

        tx_ids = list(tx_map.keys())
        metadata_list = list(bigchain.get_metadata(tx_ids))
        for metadata in metadata_list:
            tx = tx_map[metadata["id"]]
            tx.update({"metadata": metadata.get("metadata")})

        if return_list:
            tx_list = []
            for tx_id, tx in tx_map.items():
                tx_list.append(cls.from_dict(tx))
            return tx_list
        else:
            tx = list(tx_map.values())[0]
            return cls.from_dict(tx)

    type_registry = {}

    @staticmethod
    def register_type(tx_type, tx_class):
        Transaction.type_registry[tx_type] = tx_class
        


    @staticmethod
    def resolve_class(operation):
        """For the given `tx` based on the `operation` key return its
        implementation class"""
        create_txn_class = Transaction.type_registry.get(Transaction.CREATE)
        
        return Transaction.type_registry.get(operation, create_txn_class)

    @classmethod
    def validate_schema(cls, tx):
        pass

    def validate_transfer_inputs(self, bigchain, current_transactions=[]):
        # store the inputs so that we can check if the asset ids match
        
        input_txs = []
        input_conditions = []
        for input_ in self.inputs:
            input_txid = input_.fulfills.txid
            input_tx = bigchain.get_transaction(input_txid)

            if input_tx is None:
                for ctxn in current_transactions:
                    if ctxn.id == input_txid:
                        input_tx = ctxn

            if input_tx is None:
                raise InputDoesNotExist("input `{}` doesn't exist".format(input_txid))
            #This part should comment in case of shacl validation
            # if self.operation == Transaction.PRE_REQUEST:
            #     # Implement is_returned logic in the bigchain instance
            #     if bigchain.is_asset_returned(input_txid):
            #         raise DoubleSpend("Input transaction `{}` has already been returned".format(input_txid))
            # else:
            
            #     spent = bigchain.get_spent(
            #         input_txid, input_.fulfills.output, current_transactions
            #     )
            #     if spent:
            #         raise DoubleSpend("input `{}` was already spent".format(input_txid))
            #end comment area
            output = input_tx.outputs[input_.fulfills.output]
            input_conditions.append(output)
            input_txs.append(input_tx)

        # Validate that all inputs are distinct
        links = [i.fulfills.to_uri() for i in self.inputs]
        if len(links) != len(set(links)):
            raise DoubleSpend('tx "{}" spends inputs twice'.format(self.id))

        # validate asset id
        
        asset_id = self.get_asset_id(input_txs)
        
        #if self.operation == self.TRANSFER:
            # comment if shacl
            # adv_list = bigchain.get_adv_txids_for_asset(asset_id)
            # adv_txs = []
            # for adv_tx_id in adv_list:
            #     adv_tx = bigchain.get_transaction(adv_tx_id)
            #     if adv_tx.asset["data"]["status"] != "open":
            #         raise ValidationError(
            #             "The asset has an Open ADV, Transfer is not allowed".format(
            #             adv_tx_id
            #         )
            #         )       
            #end comment
            ##This part should comment if not shacl   
            
            # json_data_transfer = {
            #     "asset_ref": asset_id,
            #     "transaction_id": self.id,
            #     "operation": self.operation,
            #     "spend": asset_id,
            # }
            
            
            # script_dir = os.path.dirname(__file__)
            
            # shacl_file_path = os.path.join(script_dir, 'shacl_shape.ttl')
            
            #shacl_validator.validate_shape(json_data_transfer)
            ##end   

        tx_asset_id = ""
        if self.operation == self.BID or self.operation == self.BUYOFFER:
            tx_asset_id = self.asset["data"]["id"]
        elif self.operation == self.RETURN:
            tx_asset_id = self.asset["data"]["bid_id"]
        elif self.operation == self.ACCEPT_RETURN or self.operation == self.INTEREST or self.operation == self.PRE_REQUEST or self.operation == self.SELL:
            tx_asset_id = self.asset["data"]["asset_id"]
        
        else:
            tx_asset_id = self.asset["id"]

        if asset_id != tx_asset_id:
            raise AssetIdMismatch(
                (
                    "The asset id of the input does not"
                    " match the asset id of the"
                    " transaction"
                )
            )

        input_amount = sum(
            [input_condition.amount for input_condition in input_conditions]
        )
        output_amount = sum(
            [output_condition.amount for output_condition in self.outputs]
        )

        if output_amount != input_amount:
            raise AmountError(
                (
                    "The amount used in the inputs `{}`"
                    " needs to be same as the amount used"
                    " in the outputs `{}`"
                ).format(input_amount, output_amount)
            )

        if not self.inputs_valid(input_conditions):
            raise InvalidSignature("Transaction signature is invalid.")

        return True

    def __match_capabilities(self, bigchain, requested_cap, input_tx_id) -> bool:
        # TODO: Change input_tx_id to fulfill_tx_id
        input_tx = bigchain.get_transaction(input_tx_id)
        if input_tx is None:
            raise InputDoesNotExist("input `{}` doesn't exist".format(input_tx_id))

        input_capability_set = set()
        input_capability_list = list(input_tx.asset["data"]["capability"])
        input_capability_set.update(input_capability_list)

        requested_capability_set = set(requested_cap)
        return requested_capability_set.issubset(input_capability_set)

    def validate_interest(self, bigchain, current_transactions=[]):
        rfq_tx_id = self.asset["data"]["pre_request_id"]
        rfq_tx = bigchain.get_transaction(rfq_tx_id)

        if rfq_tx is None:
            raise InputDoesNotExist(
                "PRE_REQUEST input `{}` doesn't exist".format(rfq_tx_id)
            )

        if rfq_tx.operation != self.PRE_REQUEST:
            raise ValidationError(
                "INTEREST transaction must be against a commited PRE_REQUEST transaction"
            )

        requested_cap = rfq_tx.metadata["capability"]
        create_tx_id = self.asset["data"]["id"]

        if not self.__match_capabilities(bigchain, requested_cap, create_tx_id):
            raise InsufficientCapabilities(
                "INTEREST transaction must fulfill all the requested capabilities"
            )

        return True

    def validate_rfq(self, bigchain, current_transactions=[]):
        # pre_rfq_tx_id = self.asset["data"]["pre_request_id"]
        # pre_rfq_tx = bigchain.get_transaction(pre_rfq_tx_id)

        # # TODO: Deadline field validation
        # if rfq_tx is None:
        #     raise InputDoesNotExist(
        #         "PRE_REQUEST input `{}` doesn't exist".format(rfq_tx_id)
        #     )

        # if rfq_tx.operation != self.PRE_REQUEST:
        #     raise ValidationError(
        #         "RFQ transaction must be related to a commited PRE_REQUEST transaction"
        #     )

        return True
    
    def validate_bid(self, bigchain, current_transactions=[]):
        # FIXME: BID received for stale RFQ(timeout or fulfilled)
        rfq_tx_id = self.asset["data"]["rfq_id"]
        rfq_tx = bigchain.get_transaction(rfq_tx_id)

        if rfq_tx is None:
            raise InputDoesNotExist("RFQ input `{}` doesn't exist".format(rfq_tx_id))

        if rfq_tx.operation != self.REQUEST_FOR_QUOTE:
            raise ValidationError(
                "BID transaction must be against a commited RFQ transaction"
            )

        for output in self.outputs:
            if (
                len(output.public_keys) != 1
                or output.public_keys[0]
                != config["smartchaindb_key_pair"]["public_key"]
            ):
                raise ValidationError(
                    "BID transaction's outputs must point to Escrow account"
                )

        requested_cap = rfq_tx.metadata["capability"]
        create_tx_id = self.asset["data"]["id"]
        if not self.__match_capabilities(bigchain, requested_cap, create_tx_id):
            raise InsufficientCapabilities(
                "BID transaction must fulfill all the requested capabilities"
            )

        return self.validate_transfer_inputs(bigchain, current_transactions)
    
    
    def validate_buy_offer(self, bigchain, current_transactions=[]):
        
        adv_tx_id = self.asset["data"]["adv_id"]
        adv_tx = bigchain.get_transaction(adv_tx_id)
        #logger.debug("adv!!! %s", adv_tx)
        if adv_tx is None:
            raise InputDoesNotExist("ADV input `{}` doesn't exist".format(adv_tx_id))

        if adv_tx.operation != self.ADV:
            raise ValidationError(
                "BUYOFFER transaction must be against a commited ADV transaction"
            )

        adv_min_amt = adv_tx.metadata.get("minAmt")
        buy_offer_amt = self.metadata.get("minAmt")
        # Check if minAmt exists and compare
        if adv_min_amt is None:
            raise ValidationError("ADV transaction must have a `minAmt` specified")

        if buy_offer_amt is None or int(buy_offer_amt) < int(adv_min_amt):
            raise ValidationError(
                f"BUYOFFER amount ({buy_offer_amt}) does not meet the required minimum amount ({adv_min_amt})"
            )

        
        for output in self.outputs:
            if (
                len(output.public_keys) != 1
                or output.public_keys[0]
                != config["smartchaindb_key_pair"]["public_key"]
            ):
                raise ValidationError(
                    "BUYOFFER transaction's outputs must point to Escrow account"
                )
        #This part should comment if  shacl
        #complex validation
        # adv_status = adv_tx.metadata.get("status")
        
        # if adv_status.lower() != "open":
        #     raise ValidationError(
        #         "BUYOFFER transaction must be against an open ADV transaction"
        #     ) 
        #end
        #This part should comment if not shacl
        #start_time = time.time()
        if self.id in shacl_validator.validated_transactions:#not optimized
            #logging.info(f"Transaction {self.id} already validated.")
            return  self.validate_transfer_inputs(bigchain, current_transactions) 
        
        json_data_buy_offer = {
            "asset_ref": self.asset["data"]["id"],
            "adv_ref": self.asset["data"]["adv_id"],
            "transaction_id": self.id,
            "operation": self.operation,
            "spend": self.asset["data"]["id"],
            
        }

        validation_result = shacl_validator.validate_shape(json_data_buy_offer)
        if not validation_result: 
            raise ValidationError(
                    "BUYOFFER transaction'Validation failed"
                )
        else:
            # end_time = time.time()
            # logging.info(f"Time taken to validate buyoffer: {end_time - start_time} seconds")
        ##end
        
            return self.validate_transfer_inputs(bigchain, current_transactions) 
        
    def validate_sell(self, bigchain, current_transactions=[]):
        asset_id = self.asset["data"]["asset_id"]
        offer_id = self.asset["data"]["ref2_id"]
        adv_id = self.asset["data"]["ref1_id"]
        buy_offer_tx = bigchain.get_transaction(offer_id)
        adv_tx = bigchain.get_transaction(adv_id)
        
        if adv_tx is None:
            raise InputDoesNotExist("ADV input `{}` doesn't exist".format(adv_id))
       
        if buy_offer_tx.operation != self.BUYOFFER:
            raise ValidationError(
                "SELL transaction must be against a commited BUYOFFER transaction"
            )

        for output in self.outputs:
            if (
                len(output.public_keys) != 1
                or output.public_keys[0]
                != config["smartchaindb_key_pair"]["public_key"]
            ):
                raise ValidationError(
                    "SELL transaction's outputs must point to Escrow account"
                )
        #This part should comment in case of shacl validation  
        #complex validation 
        # adv_status = adv_tx.metadata.get("status") 
        # if adv_status.lower() != "open":
        #     raise ValidationError(
        #         "SELL transaction must be against an open ADV transaction"
        #     )
        #end comment area
        ##This part should comment if not shacl validation  
        #start_time = time.time()
        if self.id in shacl_validator.validated_transactions:
            return  self.validate_transfer_inputs(bigchain, current_transactions) 
        
        json_data_sell = {
            "asset_id": self.asset["data"]["asset_id"],
            "adv_ref": self.asset["data"]["ref1_id"],
            "buyOffer_ref": self.asset["data"]["ref2_id"],
            "transaction_id": self.id,
            "operation": self.operation,
            "spend": self.asset["data"]["asset_id"],
        }
        
        
        validation_result = shacl_validator.validate_shape(json_data_sell)
        if not validation_result: 
            raise ValidationError(
                    "SELL transaction'Validation failed"
                )
        else:
            # end_time = time.time()
            # logging.info(f"Time taken to validate sell: {end_time - start_time} seconds")
        #end
        
            return self.validate_transfer_inputs(bigchain, current_transactions) 
     
     
    
    
    @classmethod
    def handle_sell_transaction(cls,sell_data):
        """
        Update the status of the referenced ADV after a successful SELL transaction.

        Args:
            sell_data (dict): The SELL transaction data in JSON-LD format.
            graph (Graph): The RDF graph where the data is stored.
        """
        
        ttl_file_path = os.path.join(os.path.dirname(__file__), 'output.ttl')
        graph = Graph()

        # Load the RDF graph from the output.ttl file
        if os.path.exists(ttl_file_path):
            graph.parse(ttl_file_path, format="turtle")
            print(f"Loaded graph from {ttl_file_path}")
        else:
            print(f"File {ttl_file_path} does not exist.")
            return False
        # 1. Extract the ADV ID from the SELL transaction data
        adv_tx_id = sell_data.get("adv_ref")  # "ref" maps to "ex:ref" in your context
        

        if not adv_tx_id:
            print("Invalid SELL transaction: Missing adv_ref.")
            return False

        # 2. Create the URIRef for the ADV node in the RDF graph
        adv_node = URIRef("http://example.org/txn/" + adv_tx_id)
        # for s, p, o in graph.triples((adv_node, None, None)):
        #      print(f"Triple: {s} {p} {o}")
        # print("!!!!!!!! adv_node", adv_node)
        # Full URIs for properties and classes
        status_property = URIRef("http://example.org/status")
        adv_class = URIRef("http://example.org/ADV")

        
       

        # 3. Check if the ADV node exists and is of type ex:ADV
        if (adv_node, RDF.type, adv_class) in graph:
            
            open_status = Literal("Open")
            if (adv_node, status_property, open_status) in graph:
                # 5. Update the status to "Closed"
                closed_status = Literal("Closed")
                graph.set((adv_node, status_property, closed_status))
                print("ADV status successfully updated to 'Closed'.")

                # Optional: Save the updated graph back to file if necessary
                graph.serialize(destination=ttl_file_path, format="turtle")

                return True
            else:
                print("ADV transaction status is not 'Open' or not found.")
                return False
        else:
            print("ADV transaction not found in the graph.")
            return False

                   
        
    def generateShape(self):
        #commented for not shacl
        #start_time = time.time()
        if self.id in shacl_validator.create_shape_cache: #not optimized
            #logging.info(f"Transaction already processed. Skipping shape generation.")
            return True
        
        json_data = {
            "asset_id": self.id,
            "transaction_id": self.id,
            "operation": self.operation,
            
        }
        
        context = {
            "@context": {
                "ex": "http://example.org/",
                "schema": "http://schema.org/",
                "asset_id": "ex:asset_id",
                "transaction_id": "ex:transaction_id",
                "operation": "ex:operation",
                
            }
        }

        jsonld_data = {
            "@context": context["@context"],  # Reuse the existing context variable
            "@id": "http://example.org/txn/" + json_data["transaction_id"],
            "@type": "ex:" + "asset_id",
            
        }   
        
        g = Graph()
        g.parse(data=json.dumps(jsonld_data), format='json-ld')
        
        # Serialize RDF to Turtle format
        ttl_data = g.serialize(format='turtle').decode('utf-8')
        
        
        script_dir = os.path.dirname(__file__)
        ttl_file_path = os.path.join(script_dir, 'output.ttl')
        with open(ttl_file_path, 'a', encoding='utf-8') as turtle_file:
            turtle_file.write(ttl_data)
        #shacl_validator.update_existing_graph(ttl_data) 
        shacl_validator.create_shape_cache.add(self.id)
        # end_time = time.time()
        # logging.info(f"Time taken to generate shape: {end_time - start_time} seconds")    
        # logger.debug(f"Time taken to generate shape: {end_time - start_time} seconds") 
        return True
        
    def validate_adv(self, bigchain, current_transactions=[]):
        
        create_tx_id = self.asset["data"]["asset_id"]
        create_tx = bigchain.get_transaction(create_tx_id)

        if create_tx is None:
            raise InputDoesNotExist("Create input `{}` doesn't exist".format(create_tx_id))

        if create_tx.operation != self.CREATE:
            raise ValidationError(
                "ADV transaction must be against a commited CREATE transaction"
            )
        
        owener_pubkey = create_tx['outputs'][0]['public_keys']

        adv_sender_keys = create_tx['inputs'][0]['owners_before'][0]

        if adv_sender_keys not in owener_pubkey:
            raise ValidationError("Only the asset owner may advertise")


        current_state = json.dumps(create_tx, sort_keys=True)
        current_hash = hash(current_state)

        last_hash = shacl_validator.asset_state_hash.get(self.id)

        # Nothing changed, so skip shacl
        if last_hash is not None and current_hash == last_hash:
            return
            
        json_data_adv1 = {
            "asset_id": self.asset["data"]["asset_id"],
            "transaction_id": self.id,
            "operation": self.operation,
            "status":self.metadata["status"]
        }

        
        validation_result = shacl_validator.validate_shape(json_data_adv1)
        
        if not validation_result: 
            raise ValidationError(
                "SELL transaction'Validation failed"
            )

        # if validated
        shacl_validator.asset_state_hash[self.id] = current_hash
            
    def validate_update_adv(self, bigchain, current_transactions=[]):
        
        create_tx_id = self.asset["data"]["asset_id"]
        create_tx = bigchain.get_transaction(create_tx_id)

        if create_tx is None:
            raise InputDoesNotExist("Create input `{}` doesn't exist".format(create_tx_id))

        if create_tx.operation != self.CREATE:
            raise ValidationError(
                "ADV transaction must be against a commited CREATE transaction"
            )
        
        return True
        json_data_adv1 = {
            "asset_id": self.asset["data"]["asset_id"],
            "transaction_id": self.id,
            "operation": self.operation,
            "status":self.metadata["status"]
            
        }

        
        script_dir = os.path.dirname(__file__)
        
        # SHACL shapes file path
        shacl_file_path = os.path.join(script_dir, 'shacl_shape.ttl')
        

        # Validate the first advertisement
        validation_result = shacl_validator.validate_shape(json_data_adv1)
        
        if not validation_result: 
            raise ValidationError(
                    "SELL transaction'Validation failed"
                )

        
                
        

    @classmethod
    def build_exchange_tx(cls, asset_id, fulfilled_tx, recepient_pub_key):
        
        
        output_index = 0
        output = fulfilled_tx.outputs[output_index]

        buy_input =Input(
            fulfillment=output.fulfillment,
            owners_before=output.public_keys,
            fulfills=TransactionLink(asset_id, output_index),
        )
        
        buy_output = Output.generate(
            public_keys=[recepient_pub_key], amount=output.amount
        )
        
        asset = {
            
                "id": asset_id
                
            
        }
        
        metadata = {
            "requestCreationTimestamp": datetime.now().strftime("%Y-%m-%dT%H:%M:%S.%f")
        }

        buy_tx = Transaction(
            operation=Transaction.TRANSFER,
            asset=asset,
            inputs=[buy_input],
            outputs=[buy_output],
            metadata=metadata,
        )
        
        return buy_tx.sign([config["smartchaindb_key_pair"]["private_key"]])
         
        
        
        
    
    @classmethod
    def build_return_tx(cls, accept_id, asset_id, fulfilled_tx, recepient_pub_key):
        output_index = 0
        output = fulfilled_tx.outputs[output_index]

        return_input = Input(
            fulfillment=output.fulfillment,
            owners_before=output.public_keys,
            fulfills=TransactionLink(asset_id, output_index),
        )
        return_output = Output.generate(
            public_keys=[recepient_pub_key], amount=output.amount
        )

        metadata = {
            "requestCreationTimestamp": datetime.now().strftime("%Y-%m-%dT%H:%M:%S.%f")
        }
        asset = {
            "data": {
                "bid_id": asset_id,
                "accept_id": accept_id,
            }
        }
        return_tx = Transaction(
            operation=Transaction.RETURN,
            asset=asset,
            inputs=[return_input],
            outputs=[return_output],
            metadata=metadata,
        )

        return return_tx.sign([config["smartchaindb_key_pair"]["private_key"]])

    
    @classmethod
    def update_adv_metadata_on_server(cls, bigchain, adv_tx_id, new_metadata, server_keypair):
        # Fetch the original advertisement transaction
        adv_tx = bigchain.get_transaction(adv_tx_id)

        # Copy the metadata and apply updates
        updated_metadata = adv_tx.metadata.copy()  # Keep the existing metadata
        updated_metadata.update(new_metadata)  # Apply new metadata, like status

        # Create a new transaction referencing the original one, but updating only metadata
        new_tx = Transaction.create(
            inputs=[adv_tx.inputs[0]],  # Use the original transaction's input
            outputs=adv_tx.outputs,  # Use the same outputs
            asset={'id': adv_tx["data"]["asset_id"]},  # Reference the same asset
            metadata=updated_metadata  # Apply the updated metadata
        ).sign([server_keypair.private_key])  # Server signs the transaction

        # Send the transaction to BigchainDB
        bigchain.write_transaction(new_tx)

        # Return the new transaction ID
        return new_tx.id

    @classmethod
    def determine_exchanges(
        cls, bigchain, sell_id, asset_tx_id=None, adv_tx_id=None, buyer_asset_tx_id=None
    ):
        input_index = 0
        exchange_txs = list()

        if adv_tx_id is None or buyer_asset_tx_id or asset_tx_id is None:
            sell_tx = bigchain.get_transaction(sell_id)
            adv_tx_id = sell_tx.asset["data"]["ref1_id"]
            buyer_asset_tx_id = sell_tx.asset["data"]["ref2_id"]
            asset_id = sell_tx.asset["data"]["asset_id"]

        adv_tx = bigchain.get_transaction(adv_tx_id)
        if(adv_tx.operation == cls.ADV):
            seller_asset_id = adv_tx.asset["data"]["asset_id"]
            # json_data_sell = {    
            #     "adv_ref": adv_tx_id }
            # cls.handle_sell_transaction(json_data_sell)
        else:
            seller_asset_id = adv_tx.asset["id"]
        seller_asset_tx = bigchain.get_transaction(seller_asset_id)
        sell_tx = bigchain.get_transaction(sell_id)
        buyer_asset_tx = bigchain.get_transaction(buyer_asset_tx_id)

        seller_pub_key = sell_tx.inputs[input_index].owners_before[-1]
        buy_tx = Transaction.build_exchange_tx(
            buyer_asset_tx_id, buyer_asset_tx, seller_pub_key
        )
        exchange_txs.append(buy_tx)

        buyer_pub_key = buyer_asset_tx.inputs[input_index].owners_before[-1]
        buy_tx = Transaction.build_exchange_tx(
            sell_id, sell_tx, buyer_pub_key
        )
        exchange_txs.append(buy_tx)

        server_keypair = generate_keypair()  # Server's keypair for signing the transaction

        # Update the metadata by passing a dictionary
        #cls.update_adv_metadata_on_server(bigchain, adv_tx_id, {'status': 'Closed'}, server_keypair)
        
        return exchange_txs

    
    @classmethod
    def determine_returns(
        cls, bigchain, accept_id, rfq_tx_id=None, winning_bid_id=None
    ):
        input_index = 0
        return_txs = list()

        if rfq_tx_id is None or winning_bid_id is None:
            accept_tx = bigchain.get_transaction(accept_id)
            rfq_tx_id = accept_tx.asset["data"]["rfq_id"]
            winning_bid_id = accept_tx.asset["data"]["winner_bid_id"]

        rfq_tx = bigchain.get_transaction(rfq_tx_id)
        winning_bid_tx = bigchain.get_transaction(winning_bid_id)
        owned_bid_ids = bigchain.get_locked_bid_txids_for_rfq(rfq_tx_id)

        requestor_pub_key = rfq_tx.inputs[input_index].owners_before[-1]
        return_tx = Transaction.build_return_tx(
            accept_id, winning_bid_id, winning_bid_tx, requestor_pub_key
        )
        return_txs.append(return_tx)

        for bid_id in owned_bid_ids:
            if bid_id != winning_bid_id:
                bid_tx = bigchain.get_transaction(bid_id)

                # NOTE: Supports only one bidder and one input asset
                # (i.e. incompatible with divisible asset tokens)
                bidder_pub_key = bid_tx.inputs[input_index].owners_before[-1]
                return_tx = Transaction.build_return_tx(
                    accept_id, bid_id, bid_tx, bidder_pub_key
                )
                return_txs.append(return_tx)

        return return_txs

    def validate_accept(self, bigchain, current_transactions=[]):
        rfq_tx_id = self.asset["data"]["rfq_id"]
        winning_bid_id = self.asset["data"]["winner_bid_id"]

        rfq_tx = bigchain.get_transaction(rfq_tx_id)
        if rfq_tx is None or rfq_tx.operation != self.REQUEST_FOR_QUOTE:
            raise InputDoesNotExist("RFQ input `{}` doesn't exist".format(rfq_tx_id))

        accept_ffill = self.inputs[0].fulfillment.to_dict()
        for rfq_input in rfq_tx.inputs:
            rfq_ffill = rfq_input.fulfillment.to_dict()
            if rfq_ffill["public_key"] != accept_ffill["public_key"]:
                raise InvalidAccount(
                    "ACCEPT tx signer must be same as its associated RFQ(`{}`) signer".format(
                        rfq_tx_id
                    )
                )

        accept_tx = bigchain.get_accept_tx_for_rfq(rfq_tx_id)
        if accept_tx:
            raise DuplicateTransaction(
                "ACCEPT tx with the same RFQ input `{}` already committed".format(
                    rfq_tx_id
                )
            )

        winning_bid = bigchain.get_transaction(winning_bid_id)
        if winning_bid is None or winning_bid.operation != self.BID:
            raise InputDoesNotExist(
                "BID input `{}` doesn't exist".format(winning_bid_id)
            )

        winning_bid_id = self.asset["data"]["winner_bid_id"]
        owned_bid_ids = bigchain.get_locked_bid_txids_for_rfq(rfq_tx_id)

        if winning_bid_id not in owned_bid_ids:
            raise InputDoesNotExist(
                "BID input `{}` doesn't exist. Possible Causes: RFQ timeout or BID withdrawal".format(
                    winning_bid_id
                )
            )

        return True

    def validate_return(self, bigchain, current_transactions=[]):
        for input in self.inputs:
            ffill = input.fulfillment.to_dict()
            if input.owners_before[-1] != config["smartchaindb_key_pair"]["public_key"]:
                raise ValidationError("Return tx must always be initiated by Escrow")

        input_tx_id = self.asset["data"]["bid_id"]
        locked_bid_ids = set(bigchain.get_locked_bid_txids())
        if input_tx_id not in locked_bid_ids:
            raise InputDoesNotExist(
                "Escrow does not hold the bid input({})".format(input_tx_id)
            )

        return self.validate_transfer_inputs(bigchain, current_transactions)
    
    def validate_inverse_txn(self, bigchain, current_transactions=[]):
        
        
        sell_tx_id = self.asset["data"]["sell_id"]
        return_asset_tx_id = self.asset["data"]["asset_id"]
        
        sell_tx = bigchain.get_transaction(sell_tx_id)
        return_asset_tx = bigchain.get_transaction(return_asset_tx_id)
        if sell_tx is None:
            raise InputDoesNotExist("SELL input `{}` doesn't exist".format(sell_tx_id))

        if return_asset_tx.operation != self.SELL:
            raise ValidationError(
                "RETRUN SELL transaction must be against a commited SELL transaction"
            )

        for output in self.outputs:
            if (
                len(output.public_keys) != 1
                or output.public_keys[0]
                != config["smartchaindb_key_pair"]["public_key"]
            ):
                raise ValidationError(
                    "RETRUN SELL transaction's outputs must point to Escrow account"
                )
        ##This part should comment  if not shacl
        if self.id in shacl_validator.validated_transactions: #not optimized
            #logging.info(f"Transaction {self.id} already validated.")
            return  self.validate_transfer_inputs(bigchain, current_transactions) 
        json_data_accept_request_return = {
            "asset_ref": self.asset["data"]["asset_id"],
            "sell_ref": self.asset["data"]["sell_id"],
            "transaction_id": self.id,
            "operation": "REQUEST_RETURN", #self.operation,
            "spend": self.asset["data"]["asset_id"],
        }
    
        
        validation_result = shacl_validator.validate_shape(json_data_accept_request_return)
        if not validation_result: 
            raise ValidationError(
                    "RETRUN SELL transaction'Validation failed"
                )
        else:
        ##end
            return self.validate_transfer_inputs(bigchain, current_transactions) 

    def validate_accept_return(self, bigchain, current_transactions=[]):
        asset_id = self.asset["data"]["asset_id"]
        offer_id = self.asset["data"]["ref2_id"]
        adv_id = self.asset["data"]["ref1_id"]
        buy_offer_tx = bigchain.get_transaction(offer_id)
        adv_tx = bigchain.get_transaction(adv_id)
        
        if buy_offer_tx is None:
            raise InputDoesNotExist("Return request  `{}` doesn't exist".format(offer_id))

        if buy_offer_tx.operation != self.PRE_REQUEST:
            raise ValidationError(
                "ACCEPT RETURN transaction must be against a commited RETURN SELL transaction"
            )

        for output in self.outputs:
            if (
                len(output.public_keys) != 1
                or output.public_keys[0]
                != config["smartchaindb_key_pair"]["public_key"]
            ):
                raise ValidationError(
                    "ACCEPT RETURN transaction's outputs must point to Escrow account"
                )
        ##This part should comment if not shacl
        if self.id in shacl_validator.validated_transactions:#not optimized
            #logging.info(f"Transaction {self.id} already validated.")
            return self.validate_transfer_inputs(bigchain, current_transactions)  # Skip further processing if already validated
        
        json_data_accept_return = {
            "asset_id": self.asset["data"]["asset_id"],
            "sell_ref": self.asset["data"]["ref1_id"],
            "request_return_ref": self.asset["data"]["ref2_id"],
            "transaction_id": self.id,
            "operation": "ACCEPT_RETURN",#self.operation,
            "spend": self.asset["data"]["asset_id"],
        }
    
        
        
        validation_result = shacl_validator.validate_shape(json_data_accept_return)
        if not validation_result: 
            raise ValidationError(
                    "ACCEPT_RETURN transaction'Validation failed"
                )
        else:
        ##end
            return self.validate_transfer_inputs(bigchain, current_transactions) 
    
    
    
    @classmethod
    def send_transfer(cls, asset_id, fulfilled_tx, recipient_pub_key):
        """Custom transfer routine for transfering accumulated assets for a RFQ.

        NOTE: Transfer will always be triggered from the special account,
        i.e. special account secret key -> signing key.
        """
        from bigchaindb_driver import BigchainDB

        bdb = BigchainDB(os.environ.get("BIGCHAINDB_ENDPOINT"), timeout=40)

        # A `TRANSFER` transaction contains a pointer to the original asset. The original asset
        # is identified by the `id` of the `CREATE` transaction that defined it.
        transfer_asset = {"id": asset_id}

        output_index = 0
        output = fulfilled_tx.outputs[output_index]

        # Here, it defines the `input` of the `TRANSFER` transaction. The `input` contains
        # several keys:
        #
        # - `fulfillment`, taken from the previous `CREATE` transaction.
        # - `fulfills`, that specifies which condition she is fulfilling.
        # - `owners_before`.
        transfer_input = {
            "fulfillment": _fulfillment_to_details(output.fulfillment),
            "fulfills": {
                "output_index": output_index,
                "transaction_id": asset_id,
            },
            "owners_before": output.public_keys,
        }
        transfer_metadata = {
            "requestCreationTimestamp": datetime.now().strftime("%Y-%m-%dT%H:%M:%S.%f")
        }

        prepared_transfer_tx = bdb.transactions.prepare(
            operation="TRANSFER",
            asset=transfer_asset,
            inputs=transfer_input,
            metadata=transfer_metadata,
            recipients=recipient_pub_key,
        )

        # signs tx with the special account's private key
        fulfilled_transfer_tx = bdb.transactions.fulfill(
            prepared_transfer_tx,
            private_keys=config["smartchaindb_key_pair"]["private_key"],
        )

        bdb.transactions.send_async(fulfilled_transfer_tx)